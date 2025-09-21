# syntax=docker/dockerfile:1.7

# ---- builder ----
FROM node:20-alpine AS builder
WORKDIR /app
RUN corepack enable && corepack prepare pnpm@10.16.1 --activate

# Copy only manifests first (better cache)
COPY services/claims-api-ts/package.json services/claims-api-ts/pnpm-lock.yaml ./
RUN pnpm install --frozen-lockfile

# Now the sources
COPY services/claims-api-ts ./
RUN pnpm build

# ---- runtime ----
FROM node:20-alpine AS runtime
WORKDIR /app
ENV NODE_ENV=production
RUN corepack enable && corepack prepare pnpm@10.16.1 --activate

# Bring over the app artifacts and prod deps
COPY --from=builder /app/package.json /app/pnpm-lock.yaml ./
COPY --from=builder /app/node_modules ./node_modules
COPY --from=builder /app/dist ./dist

EXPOSE 8080
CMD ["node", "dist/server.js"]
