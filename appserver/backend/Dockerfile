FROM node

WORKDIR /app

COPY package*.json /app/
RUN npm ci

COPY . /app/

RUN [ "npm", "run", "swagger" ]

CMD [ "npm", "run" ]