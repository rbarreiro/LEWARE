const express = require('express');
const Joi = require('joi');
const app = express();
const port = 3000;
const swaggerUi = require('swagger-ui-express');
const swaggerDocument = require('./swagger.json');
const r = require('rethinkdb');

const pages = {};

function onAppChanges(conn){
    r.db("appserver").table("apps").changes(includeInitial = true).run(conn, (err, cursor)=>{
        if (err) throw err;
        cursor.each((err, row)=>{
            if (err) throw err;
            pages[row.new_val.id] = row.new_val.page;      
        })
    })
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
    services : Joi.string().required()
});

app.post('/upsertapp', (req, res) => {
    const { error, value } = newappSchema.validate(req.body);
    if (error) {
        return res.status(400).send(error.details[0].message);
    }
    r.db('appserver').table("apps").get(value.id).replace(value)
    .run(connection, (err, r)=>{
        if (err) throw err;
        res.send(r)
    })
});

app.get('/app/:id', (req, res) => {
    res.send(pages[req.params.id]);
});

app.listen(port, () => {
  console.log(`appserver listening on port ${port}`)
});