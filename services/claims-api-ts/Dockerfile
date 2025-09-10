### build
FROM node:22-alpine as build
WORKDIR /app
RUN npm i -g pnpm@9.5
COPY . .
RUN pnpm i --frozen-lockfile
RUN pnpm --filter claims-core-ts build
RUN pnpm --filter claims-api-ts build

### deploy
FROM node:22-alpine as deploy
WORKDIR /app
RUN npm i -g pnpm@9.5
COPY --from=build /app .
RUN pnpm deploy --filter ...claims-api-ts --prod /deploy

### runtime
FROM node:22-alpine
WORKDIR /app
COPY --from=deploy /deploy .
ENV NODE_ENV=production
EXPOSE 8787
CMD ["node", "dist/server.js"]
