# Public-repository clean-container reproduction

Date: 2026-08-24/25 UTC
Result: **PASS**

## Public run

- Repository: <https://github.com/ajogalekar/rna-at-most-two-short-helices>
- Public commit tested:
  `237eb30fe5eb39b3c82a3cb859c17e8c6cf2613c`
- GitHub Actions run:
  <https://github.com/ajogalekar/rna-at-most-two-short-helices/actions/runs/32788789840>
- Workflow: `.github/workflows/clean-container-reproduction.yml`
- Outcome: success in 1 hour 8 minutes 44 seconds

The job started with the digest-pinned image
`ubuntu:24.04@sha256:33ceb71981b602c1a7443a53469e4dba065f7503eab3078a2d7a57a2ab987517`,
initialized an empty Git repository inside the container, fetched the public
branch, and required the fetched commit to equal the expected public commit.
No dependency or project build cache was restored.

## Pinned environment

- Architecture: `x86_64`
- Elan installer commit:
  `7dbaedfc33d255f744d959e65ff4241216f8a9ac`
- Elan installer SHA-256:
  `a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53`
- Lean toolchain: `leanprover/lean4:v4.34.0-rc1`
- Lake: `5.0.0-src+3447a66`
- Mathlib revision:
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`

## Commands and observed result

The command executed from the fresh public clone was the bare default build:

```sh
lake build
```

Its terminal result was:

```text
Build completed successfully (3070 jobs).
```

The job then ran:

```sh
lake env lean RNA/AtMostTwoShort/AxiomAudit.lean
```

and required the following declaration and exact kernel-reported axiom line:

```text
RNA.atMostTwoShortHelixDesignability : AtMostTwoShortHelixDesignabilityStatement
'RNA.atMostTwoShortHelixDesignability' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The independent ordinary release CI also passed at that public commit:
<https://github.com/ajogalekar/rna-at-most-two-short-helices/actions/runs/32788781819>.

## Direct checks of public bytes

Files downloaded from `raw.githubusercontent.com` at the tested commit had
these SHA-256 digests:

- manuscript PDF:
  `9c6cd4c7fcb333944b5a2853edbd9fcc9d7f40fa5feafac81d50c1e3e32397e2`;
- manuscript TeX:
  `d2b5166aff11c6a64d494b93ab1f7a3af8ecaf1652670fbb0c8ccc383ee2788a`;
- canonical proof specification:
  `fb9bee1126791b9ca53b3903c061df27e3856dd20b9c7fc248b7acd4e5326841`;
  and
- formalization-metrics report:
  `b97a0465d97c9568211cf959e35569a4f82c766f511ca553fd1dd6ef1e1433f9`.

## Local Docker resource note

A fully cold local Docker Desktop attempt reached the terminal project modules
but was killed with exit code 137 while elaborating memory-intensive regression
example modules. The Docker engine exposed 8,322,359,296 bytes of memory; the
theorem module itself had already built. Reducing visible CPUs did not make the
largest individual module fit. This was a host-memory limit, not a Lean error.
The public hosted container run above, using the same pinned sources and bare
build command, completed all 3,070 jobs and the final axiom audit. The local
Docker recipe therefore documents that the engine must be allocated more than
8 GB.
