const swaggerAutogen = require('swagger-autogen')()

const outputFile = './swagger-output.json';
const routes = ['./index.js'];

swaggerAutogen(outputFile, routes, doc);