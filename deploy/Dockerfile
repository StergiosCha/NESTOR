# NESTOR Phase 2 runner: Coq + Python in one image.
#
# The target is linux/amd64, so coqc comes from the distro (no Rosetta, no
# OCAMLLIB dance). The platform is NOT pinned on this FROM line: `az acr
# build`'s dependency scanner cannot parse `FROM --platform=...` and fails
# with "unable to understand line". ACR agents are already linux/amd64, so
# the flag is redundant there. Building locally on an arm64 Mac instead?
# Pass it on the command line:
#   docker build --platform linux/amd64 -f deploy/Dockerfile .
FROM python:3.11-slim

# Required: coqc, and a toolchain for any wheel that needs compiling.
RUN apt-get update && apt-get install -y --no-install-recommends \
        coq build-essential \
    && rm -rf /var/lib/apt/lists/*

# prover9 + mace4 for the FOL pipeline.
#
# This was previously a best-effort install with `|| echo WARNING`. That was
# wrong: the apt package is not present in this base image, the build passed
# anyway, and all 12 FOL containers then died on `FATAL: prover9 not on PATH`
# having burned a container each. A dependency the pipeline cannot run
# without must fail the BUILD.
#
# Try apt first (cheap when the package exists), then fall back to building
# LADR from source, which is where prover9/mace4 actually come from.
RUN set -eux; \
    apt-get update; \
    if apt-get install -y --no-install-recommends prover9; then \
        echo "prover9 from apt"; \
    else \
        echo "apt has no prover9; building LADR from source"; \
        apt-get install -y --no-install-recommends curl ca-certificates; \
        cd /tmp; \
        # http, not https: the host's TLS handshake fails (UNEXPECTED_EOF).
        # Verified: 1,795,750 bytes, `make all` exits 0, and the built
        # prover9 proves a smoke theorem.
        curl -fsSL -o ladr.tar.gz \
          http://www.cs.unm.edu/~mccune/prover9/download/LADR-2009-11A.tar.gz; \
        tar xzf ladr.tar.gz; \
        cd LADR-2009-11A; \
        # Two portability faults in this 2009 code under a modern toolchain:
        #  1. GCC 14 rejects K&R function definitions -> -std=gnu89 accepts them.
        #  2. The Makefiles hardcode `-lm` BEFORE the object files. GNU ld
        #     resolves left-to-right, so math symbols (round) stay undefined:
        #     "undefined reference to `round'". (macOS ld ignores order, so it
        #     builds there.) A gcc wrapper that appends -lm to EVERY invocation
        #     fixes the link regardless of which Makefile does it; a trailing
        #     -lm on a -c compile is simply ignored.
        printf '#!/bin/sh\nexec gcc "$@" -lm\n' > /usr/local/bin/gcc-lm; \
        chmod +x /usr/local/bin/gcc-lm; \
        make all CC=gcc-lm CFLAGS="-O -w -std=gnu89"; \
        install -m 0755 bin/prover9 bin/mace4 bin/interpformat \
                        bin/prooftrans /usr/local/bin/; \
        cd /; rm -rf /tmp/LADR-2009-11A /tmp/ladr.tar.gz; \
    fi; \
    rm -rf /var/lib/apt/lists/*

# Verify at BUILD time, the same way coqc is verified. A trivial valid proof
# must go through, or the image is not fit to run the FOL grid.
RUN set -eux; \
    printf 'formulas(assumptions).\n all x (p(x) -> q(x)).\n p(a).\nend_of_list.\nformulas(goals).\n q(a).\nend_of_list.\n' > /tmp/t.in; \
    prover9 -f /tmp/t.in | grep -q "THEOREM PROVED"; \
    echo "prover9 OK: $(command -v prover9)"; \
    # mace4 only needs to exist and be runnable -- do NOT run it on the proof
    # test above, which is unsatisfiable (the goal follows from the premises),
    # so mace4 would search ever-larger domains forever and hang the build.
    # A trivially satisfiable one-clause problem, capped hard, confirms it runs.
    printf 'formulas(assumptions).\n p(a).\nend_of_list.\n' > /tmp/m.in; \
    timeout 20 mace4 -n 2 -m 1 -f /tmp/m.in >/dev/null 2>&1; \
    test -x "$(command -v mace4)"; \
    echo "mace4 OK:   $(command -v mace4)"; \
    rm -f /tmp/t.in /tmp/m.in

# Verify coqc at BUILD time -- a broken compiler must fail the build,
# not silently turn every item into a "coqc_missing" error at run time.
RUN printf 'Theorem t : True.\nProof. exact I. Qed.\n' > /tmp/t.v \
    && coqc /tmp/t.v && echo "coqc OK: $(coqc --version | head -1)"

# Record the compiler version in the image itself. Every cell of the grid
# must be compiled by the SAME coqc: what compiles changes between
# versions, so a grid whose cells used different compilers is not
# internally comparable. Baking the version in lets a results file be
# checked against the image that produced it.
RUN coqc --version | head -1 > /etc/nestor-coqc-version && \
    cat /etc/nestor-coqc-version

WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .
# PROVER9_PATH/MACE4_PATH are bare names so they resolve wherever the
# install landed (/usr/bin from apt, /usr/local/bin from source).
ENV COQC_PATH=/usr/bin/coqc \
    COQ_TIMEOUT=60 \
    PROVER9_PATH=prover9 \
    MACE4_PATH=mace4 \
    PROVER_TIMEOUT=30 \
    PYTHONUNBUFFERED=1 \
    LLM_TIMEOUT=300 \
    LLM_MAX_RETRIES=5

# Results go to whatever OUTDIR the cell script is given (/results in the
# Azure form). Mount a volume there or the container leaves with them.
# bash, not python: the cell script sets up and then calls the pipeline.
ENTRYPOINT ["bash"]
CMD ["deploy/run_one_cell.sh"]
