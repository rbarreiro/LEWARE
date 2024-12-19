const swaggerAutogen = require('swagger-autogen')()

const outputFile = './swagger-output.json';
const routes = ['./index.js'];

const doc = {
  info: {
    title: 'App Server',
  },
  host : ""
};

swaggerAutogen(outputFile, routes, doc);