
# Multi-workspace build for claims-api using pnpm
FROM node:20-alpine AS base
ENV PNPM_HOME=/root/.local/share/pnpm
ENV PATH=$PNPM_HOME:$PATH
RUN corepack enable

WORKDIR /app

# Copy workspace manifests
COPY package.json pnpm-workspace.yaml ./
COPY packages/claims-core-ts/package.json packages/claims-core-ts/package.json
COPY services/claims-api-ts/package.json services/claims-api-ts/package.json

# Install workspace deps (no lockfile in this skeleton; allow network resolutions)
RUN pnpm install --frozen-lockfile=false

# Copy sources
COPY packages/ ./packages/
COPY services/ ./services/

# Build TypeScript packages we need
RUN pnpm -C packages/claims-core-ts build && pnpm -C services/claims-api-ts build

ENV PORT=8787
ENV HOST=0.0.0.0
EXPOSE 8787

CMD ["node", "services/claims-api-ts/dist/server.js"]
