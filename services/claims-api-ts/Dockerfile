# syntax=docker/dockerfile:1.7

ARG NODE_BASE=node:20-alpine@sha256:6a91081a440be0b57336fbc4ee87f3dab1a2fd6f80cdb355dcf960e13bda3b59

########################
# build (with deploy)
########################
FROM ${NODE_BASE} AS build
ENV CI=true
ENV NODE_ENV=production
WORKDIR /repo

ARG PNPM_VERSION=10.16.1
RUN corepack enable && corepack prepare pnpm@${PNPM_VERSION} --activate

# workspace roots first
COPY pnpm-workspace.yaml pnpm-lock.yaml package.json .npmrc ./

# service + core manifests
COPY packages/claims-core-ts/package.json packages/claims-core-ts/package.json
COPY services/claims-api-ts/package.json services/claims-api-ts/package.json

# prefetch just what we need (closure) and exclude root
RUN --mount=type=cache,id=pnpm-store,target=/root/.local/share/pnpm/store \
  pnpm fetch \
    --filter "./services/claims-api-ts..." \
    --filter "./packages/claims-core-ts..." \
    --filter "!@workspace:root"

# sources
COPY packages/ ./packages/
COPY services/ ./services/

# install only those two (exclude root), build them
RUN --mount=type=cache,id=pnpm-store,target=/root/.local/share/pnpm/store \
  pnpm install --frozen-lockfile \
    --filter "./services/claims-api-ts..." \
    --filter "./packages/claims-core-ts..." \
    --filter "!@workspace:root" \
  && pnpm -r -F "claims-core-ts" -F "claims-api-ts" build

# make a self-contained /deploy without 'pnpm deploy'
RUN set -eux; \
  cd services/claims-api-ts; \
  pnpm install --prod --frozen-lockfile --link-workspace-packages; \
  mkdir -p /deploy; \
  cp -R dist package.json node_modules /deploy/

########################
# runtime
########################
FROM ${NODE_BASE} AS runtime
ENV NODE_ENV=production
ENV PORT=8787
ENV HOST=0.0.0.0
WORKDIR /app
COPY --from=build /deploy ./
EXPOSE 8787
CMD ["node", "dist/server.js"]
