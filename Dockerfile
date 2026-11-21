FROM node:22-alpine
WORKDIR /app
COPY server.mjs package.json ./
RUN mkdir -p /app/data && chmod 777 /app/data
ENV PORT=7860
EXPOSE 7860 8080
CMD ["node", "server.mjs"]
