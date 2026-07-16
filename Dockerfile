# Full image: server + pinned Lean/Mathlib verifier. WARNING: the Mathlib cache makes
# this image large (several GB) and the first build slow. For a quick look, skip Docker
# and run the offline demo instead (see README).
FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive PATH="/root/.elan/bin:${PATH}"
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl git ca-certificates python3 python3-pip && rm -rf /var/lib/apt/lists/*
WORKDIR /brigade
COPY server/ server/
COPY scripts/ scripts/
COPY lean/ lean/
RUN pip3 install --break-system-packages -e server/ pytest pytest-asyncio
RUN bash scripts/setup_lean.sh
ENV LEAN_MODE=file LEAN_PROJECT_DIR=/brigade/lean/BrigadeLean HOST=0.0.0.0 PORT=8811
EXPOSE 8811
CMD ["bash", "scripts/run_server.sh"]
