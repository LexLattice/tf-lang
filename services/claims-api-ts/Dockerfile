# syntax=docker/dockerfile:1.7

########################
# build (with deploy)
########################
FROM node:20-alpine AS build
ENV PNPM_HOME=/root/.local/share/pnpm
ENV PATH=$PNPM_HOME:$PATH
RUN corepack enable
WORKDIR /repo

# copy manifests first for caching
COPY pnpm-workspace.yaml pnpm-lock.yaml package.json ./
COPY packages/claims-core-ts/package.json packages/claims-core-ts/package.json
COPY services/claims-api-ts/package.json services/claims-api-ts/package.json

# fetch deps into PNPM store cache
RUN --mount=type=cache,id=pnpm-store,target=/root/.local/share/pnpm/store \
    pnpm fetch

# bring sources
COPY packages/ ./packages/
COPY services/ ./services/

# install, build, and deploy only the service to /deploy
RUN --mount=type=cache,id=pnpm-store,target=/root/.local/share/pnpm/store \
    pnpm i --frozen-lockfile && \
    pnpm -r -F "claims-core-ts" -F "claims-api-ts" build && \
    pnpm deploy --legacy --filter claims-api-ts /deploy

########################
# runtime
########################
FROM node:20-alpine AS runtime
ENV NODE_ENV=production
ENV PORT=8787
ENV HOST=0.0.0.0
WORKDIR /app
COPY --from=build /deploy ./
EXPOSE 8787
CMD ["node", "dist/server.js"]
