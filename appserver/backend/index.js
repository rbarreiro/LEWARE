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

function onAppChanges(conn){
    r.db("appserver").table("apps").wait().run(conn, (err, res)=>{
        if (err) throw err;
        r.db("appserver").table("apps")
        .changes({includeInitial : true}).run(conn, (err, cursor)=>{
            if (err) throw err;
            cursor.each((err, row)=>{
                if (err) throw err;
                pages[row.new_val.id] = row.new_val.page;      
                const isolate = new ivm.Isolate({ memoryLimit: 128 });
                const context = isolate.createContextSync();
                const jail = context.global;
                jail.setSync('global', jail.derefInto());
                jail.setSync('log', function(...args) {
                    console.log(...args);
                });
                context.eval(row.new_val.server).then(servs=>{
                    services[row.new_val.id] = servs;
                }).catch(err=>{
                    console.log(err);
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
            r.db("appserver").tableCreate("apps")
        ],
        null
    ).run(conn, (err, res)=>{
        if (err) throw err;
        console.log(res)
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
    server : Joi.string().required()
}).required();

app.post('/upsertapp', (req, res) => {
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