const express = require('express');
const Joi = require('joi');
const app = express();
const port = 3000;
const swaggerUi = require('swagger-ui-express');
const swaggerDocument = require('./swagger-output.json');
const r = require('rethinkdb');

var connection = null;
r.connect( {host: 'rethinkdb', port: 28015}, function(err, conn) {
    if (err) throw err;
    r.branch(
        r.dbList().contains("appserver").not(), 
        [
            r.dbCreate("appserver"),
            r.db("appserver").tableCreate("apps")
        ]
    ).run(conn, (err, res)=>{
        if (err) throw err;
        console.log(res)
    })
    connection = conn;
});

app.use('/docs', swaggerUi.serve, swaggerUi.setup(swaggerDocument));

app.use(express.json());

app.get('/', (req, res) => {
    r.db("appserver").table("apps").pluck("name").coerceTo('array').run(conn, (err, res)=>{
        if (err) throw err;
        res.send(res)
    })
})

const newappSchema = Joi.object({
    id : Joi.string().required(), 
    page : Joi.string().required(),
    services : Joi.string().required()
});

app.put('/newapp', (req, res) => {
    const { error, value } = newappSchema.validate(req.body);
    if (error) {
        return res.status(400).send(error.details[0].message);
    }
    r.db('appserver').table("apps").insert(value)
});


app.listen(port, () => {
  console.log(`appserver listening on port ${port}`)
});