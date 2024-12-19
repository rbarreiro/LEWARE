const swaggerAutogen = require('swagger-autogen')()

const outputFile = './swagger-output.json';
const routes = ['./index.js'];

const doc = {
  info: {
    title: 'App Server',
  },
};

swaggerAutogen(outputFile, routes, doc);