# Clean-container reproduction

This recipe starts from the digest-pinned Ubuntu image, verifies a
commit-pinned Elan installer by SHA-256, fetches the requested public Git
reference, lets the repository's `lean-toolchain` select Lean, builds the
default Lake target, and asks Lean to print the theorem and its transitive
axiom set.

Build the clean image from the repository root, then run the check with two
visible CPUs so Lake does not oversubscribe memory on high-core Docker hosts:

```sh
docker build --no-cache --progress=plain \
  -f reproducibility/Dockerfile \
  -t rna-at-most-two-reproduction .

docker run --rm --cpuset-cpus=0-1 rna-at-most-two-reproduction
```

To reproduce a release tag or exact commit rather than the default public
branch, pass `--build-arg REPOSITORY_REF=<tag-or-commit>`.

The build fails unless the audit output contains both
`RNA.atMostTwoShortHelixDesignability` and the exact axiom line
`[propext, Classical.choice, Quot.sound]`.

The CPU cap changes only scheduling and peak memory.  The command executed in
the fresh public clone is the repository's bare `lake build`; the pinned Lean
and Mathlib versions and all checked source bytes are unchanged.
