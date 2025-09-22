# syntax=docker/dockerfile:1.7

# ---- builder ----
FROM node:20-alpine AS builder
WORKDIR /app
RUN corepack enable && corepack prepare pnpm@10.16.1 --activate

# Workspace manifests for reproducible installs
COPY package.json pnpm-lock.yaml pnpm-workspace.yaml ./

# Bring in workspace packages and the service sources
COPY packages ./packages
COPY services/claims-api-ts ./services/claims-api-ts

# Install only what the service needs and build artifacts
RUN pnpm install --filter ./services/claims-api-ts --frozen-lockfile
RUN pnpm --filter ./services/claims-api-ts build

# ---- runtime ----
FROM node:20-alpine AS runtime
WORKDIR /app
ENV NODE_ENV=production
RUN corepack enable && corepack prepare pnpm@10.16.1 --activate

# Bring over the app artifacts and prod deps
COPY --from=builder /app/services/claims-api-ts/package.json ./package.json
COPY --from=builder /app/services/claims-api-ts/node_modules ./node_modules
COPY --from=builder /app/services/claims-api-ts/dist ./dist

EXPOSE 8080
CMD ["node", "dist/server.js"]
