const express = require('express');
const Joi = require('joi');
const app = express();
var expressWs = require('express-ws')(app);
const port = 3000;
const swaggerUi = require('swagger-ui-express');
const swaggerDocument = require('./swagger.json');
const r = require('rethinkdb');
const ivm = require('isolated-vm');


const pages = {};
const services = {};

function runMigrations(conn, context, appId, migrations, then){
    r.db("appserver").table("migration_status").get(appId).run(conn, (err, doneMigrations)=>{
        if (err) throw err;
        if (res == null){
            doneMigrations = [];
        }
        if (doneMigrations.length > migrations.length){
            console.log("Migration error: ", appId, " has less migrations than expected")
            return;
        }

        const queries = [];
        for(let i = 0; i < migrations.length; i++){
            if(doneMigrations.length <= i){
                queries.push(context.evalSync(migrations[i])());                
            }else{
                if (doneMigrations[i] != migrations[i]){
                    console.log("Migration error: ", appId, ", ", i, " has different migration than expected")
                    return;
                }
            }
        }
        if(queries.length > 0){
            queries.push(r.db("appserver").table("migration_status").get(appId).replace({id: appId, migrations: migrations}));
            r.expr(queries).run(conn, (err, res)=>{
                if(err) throw err;
                then();
            });
        }else{
            then();
        }
        
    });
}


function onAppChanges(conn){
    r.expr([r.db("appserver").table("apps").wait(), r.db("appserver").table("migration_status").wait()]).run(conn, (err, res)=>{
        if (err) throw err;
        r.db("appserver").table("apps")
        .changes({includeInitial : true}).run(conn, (err, cursor)=>{
            if (err) throw err;
            cursor.each((err, row)=>{
                if (err) throw err;
                r.branch(
                    r.dbList().contains("app_" + row.new_val.id).not(), 
                    r.dbCreate("app_" + row.new_val.id),
                    null
                ).run(conn, (err, res)=>{
                    if (err) throw err;
                    pages[row.new_val.id] = row.new_val.page;      
                    const isolate = new ivm.Isolate({ memoryLimit: 128 });
                    const context = isolate.createContextSync();
                    const jail = context.global;
                    jail.setSync('global', jail.derefInto());
                    jail.setSync('log', function(...args){
                        console.log(...args);
                    });
                    runMigrations(conn, context, row.new_val.id, row.new_val.migrations, ()=>{
                        console.log("launching server for ", row.new_val.id)
                        context.eval(row.new_val.server).then(servs=>{
                            services[row.new_val.id] = servs;
                        }).catch(err=>{
                            console.log(err);
                        });

                    });
                });
            })
        });
    });
}


var connection = null;
r.connect( {host: 'rethinkdb', port: 28015}, function(err, conn) {
    if (err) throw err;
    r.branch(
        r.dbList().contains("appserver").not(), 
        [
            r.dbCreate("appserver"),
            r.db("appserver").tableCreate("apps"),
            r.db("appserver").tableCreate("migration_status")
        ],
        null
    ).run(conn, (err, res)=>{
        if (err) throw err;
        connection = conn;
        onAppChanges(conn);
    })
});

app.use('/docs', swaggerUi.serve, swaggerUi.setup(swaggerDocument));

app.use(express.json());

app.get('/', (req, res) => {
    r.db("appserver").table("apps").pluck("id").coerceTo('array')
    .run(connection, (err, r)=>{
        if (err) throw err;
        res.send(r)
    })
})

const newappSchema = Joi.object({
    id : Joi.string().required(), 
    page : Joi.string().required(),
    server : Joi.string().required(),
    migrations : Joi.array().items(Joi.string()).required(),
}).required();

app.post('/upsertapp', (req, res) => {
    console.log(req.body)
    const { error, value } = newappSchema.validate(req.body);
    if (error) {
        return res.status(400).send(error.details[0].message);
    }
    r.db('appserver').table("apps").get(value.id).replace(value)
    .run(connection, (err, r)=>{
        if (err) throw err;
        console.log(value.id, "updated")
        res.send(r)
    })
});

app.get('/app/:id', (req, res) => {
    res.send(pages[req.params.id]);
});

const serviceCallSchema = Joi.object({
    service : Joi.string().required(),
    reqId : Joi.string().required(),
}).required();

app.ws('/appcom/:id', function(ws, req) {
  ws.on('message', function(msg) {
    const { error, value } = serviceCallSchema.validate(JSON.parse(msg));
    if (error) {
        console.log(error.details[0].message);
    }else{
        console.log(value);
    }
  });
});

app.listen(port, () => {
  console.log(`appserver listening on port ${port}`)
});