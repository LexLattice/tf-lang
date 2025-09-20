# Minimal reproducible environment for CI/local parity
FROM node:20-bullseye
WORKDIR /repo
COPY package*.json ./
RUN npm ci || true
COPY . .
CMD ["bash","-lc","npm run a0 && npm run a1 && npm test"]
