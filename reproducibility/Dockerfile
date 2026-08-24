FROM ubuntu:24.04@sha256:33ceb71981b602c1a7443a53469e4dba065f7503eab3078a2d7a57a2ab987517

ARG REPOSITORY_URL=https://github.com/ajogalekar/rna-at-most-two-short-helices.git
ARG REPOSITORY_REF=final-publication-release
ARG ELAN_COMMIT=7dbaedfc33d255f744d959e65ff4241216f8a9ac
ARG ELAN_INIT_SHA256=a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
       build-essential ca-certificates curl git \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL \
      "https://raw.githubusercontent.com/leanprover/elan/${ELAN_COMMIT}/elan-init.sh" \
      -o /tmp/elan-init.sh \
    && echo "${ELAN_INIT_SHA256}  /tmp/elan-init.sh" | sha256sum -c - \
    && sh /tmp/elan-init.sh -y --default-toolchain none \
    && rm /tmp/elan-init.sh

ENV PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

WORKDIR /work
RUN git init repo \
    && cd repo \
    && git remote add origin "${REPOSITORY_URL}" \
    && git fetch --depth 1 origin "${REPOSITORY_REF}" \
    && git checkout --detach FETCH_HEAD
WORKDIR /work/repo

RUN git rev-parse HEAD \
    && cat lean-toolchain \
    && lake --version

CMD ["bash", "-lc", "set -o pipefail; lake build && lake env lean RNA/AtMostTwoShort/AxiomAudit.lean 2>&1 | tee /tmp/RNA_AT_MOST_TWO_AXIOM_AUDIT.txt && grep -F 'RNA.atMostTwoShortHelixDesignability' /tmp/RNA_AT_MOST_TWO_AXIOM_AUDIT.txt && grep -F \"'RNA.atMostTwoShortHelixDesignability' depends on axioms: [propext, Classical.choice, Quot.sound]\" /tmp/RNA_AT_MOST_TWO_AXIOM_AUDIT.txt"]
