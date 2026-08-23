# Theorem closure identity report

Date: 2026-08-22

- Branch: `final-publication-release`
- Baseline commit: `28070dd0032f417b1eed03a1fa23f81a260eaff7`
- Result: **PASS**

## Identity result

Before any publication-example edit, SHA-256 was computed for every Lean
source returned by `git ls-files '*.lean'`.  The same computation was repeated
after both new modules had compiled.  The two maps contain the same 60 paths,
and every corresponding digest is identical.  Thus no pre-existing tracked
Lean source changed.

## Exact comparison with the isolated qualification baseline

The final 46-file theorem closure was rechecked path-by-path against the
authoritative pre-build hash inventory from the isolated qualification run:

```text
closure list:
/Users/ashujo/Documents/Science/rna_at_most_two_release_qualification/isolated_run/final_dependency_closure.txt
SHA-256 4dda2cb3d78cec0bb6c5dd34237abe05ec0a35903a9e4beb24979ff4d3256d34

baseline hash inventory:
/Users/ashujo/Documents/Science/rna_at_most_two_release_qualification/isolated_run/source_hashes_before.sha256
SHA-256 dad0ea8a1c1c8b3304ab825b8ab2bea96c840caefe8e38ad5f912d45f34f3811
```

Leading `./` components were normalized before matching paths.  The closure
manifest contains 46 entries and 46 unique paths.  The baseline inventory
contains 104 entries and 104 unique paths.  Every closure path occurs exactly
once in the baseline inventory, every current closure file exists, and every
current SHA-256 digest equals its recorded pre-build digest.

| Exact comparison check | Result |
|---|---:|
| Closure paths compared | 46 |
| Exact digest matches | **46 / 46** |
| Closure paths absent from baseline inventory | 0 |
| Closure paths absent from current repository | 0 |
| Baseline duplicate paths | 0 |
| Digest mismatches | 0 |

This comparison is independent of the broader 60-file before/after map below
and directly establishes byte identity for the authoritative final theorem
dependency closure against `isolated_run/source_hashes_before.sha256`.

For portable rechecking, the release also includes
docs/THEOREM_CLOSURE_BASELINE.sha256, a 46-line closure-only sidecar derived
from that authoritative inventory. Its SHA-256 is
6bac213301f3449dd961aa231480bfdf84db282eda98f8bc2f63fa81941d8f41;
running shasum -a 256 -c docs/THEOREM_CLOSURE_BASELINE.sha256 from the
repository root reports 46 successful matches.

The only new Lean sources are:

- `RNA/AtMostTwoShort/PublicationExamples.lean`;
- `RNA/AtMostTwoShort/PublicationExamplesAxiomAudit.lean`.

The new modules are downstream-only.  `PublicationExamples` imports
`RNA.AtMostTwoShort.Examples`; `PublicationExamplesAxiomAudit` imports
`PublicationExamples`.  Neither `RNA.lean`,
`RNA.AtMostTwoShort.Designability`, nor any other pre-existing Lean source
imports either new module.  Therefore the source and import closure of
`RNA.atMostTwoShortHelixDesignability` is unchanged.

## Validation

The following builds completed successfully:

```text
lake build RNA.AtMostTwoShort.PublicationExamples
Build completed successfully (3056 jobs).

lake build RNA.AtMostTwoShort.PublicationExamplesAxiomAudit
Build completed successfully (3057 jobs).

lake build RNA.AtMostTwoShort.Designability
Build completed successfully (3053 jobs).
```

The first module checks these publication endpoints:

- `t1Target = (())(())((()))` is in `InTargetClassKLeTwo`, has seven
  target pairs, and is uniquely designed by literal `w1 = AGCUUGCAGGGCCC`;
- `t2Target = (((((((())(()))))((())))))` is in
  `InTargetClassKLeTwo`, has thirteen target pairs, and is uniquely designed
  by corrected literal `w2 = GGGAGGAGCUUGCACCUGGGCCCCCC`; its coloring has
  the deterministic F/Q helix pattern `BBB`, `GBB`, `GB`, `GB`, `BBB`, and
  the audit checks the named-residue theorem with `xi = 0` (`eta = 1`);
- `threeShortTarget = ((.))((.))((.))` has short-helix count three and is
  rejected by `InTargetClassKLeTwo`;
- the explicit length-one maximal-helix target is rejected;
- `AUAU` does not uniquely design the nested target `(())`; and
- ordinary kernel reduction over all `3^6 = 729` colorings proves that the
  three-short target has no coloring that is both proper and strongly
  modulo-2 separated.

The literal-word theorems do not invoke an external folding oracle.  Each
word is proved equal to `sequenceOfProperColoring` for an explicit proper
strongly separated coloring, after which
`uniqueDesigns_sequenceOfProperSeparatedColoring` supplies the universal
strict no-tie result over every compatible noncrossing partial matching.

The standalone audit reports exactly the following transitive dependency set
for every audited publication endpoint:

```text
[propext, Classical.choice, Quot.sound]
```

A token-aware scan of the two new Lean files found no occurrence of `sorry`,
`admit`, a custom `axiom` declaration, `unsafe`, `sorryAx`, or
`native_decide`.  A trailing-whitespace scan also returned no matches.

## Pre-existing tracked Lean-source SHA-256 map

The following map was identical before and after the publication-example
work:

```text
13eb6f79a64a2a80fe5526330799fe79f8a0b46a9e0ef7aad542c33b126b6e5a  RNA.lean
da4bc09c95a4b23b73ebc2493881ccafee46362c6aebefe95d18fb2f9c5e258f  RNA/Alphabet.lean
ae89d4686005683925f6adb7e5583f4df3f94cf91417799c9a7e6231493d9e1a  RNA/AtMostTwoShort/AxiomAudit.lean
14336b0650651ea64387637318dd0005d0ce5d8239f50228e1025d6cc733c36e  RNA/AtMostTwoShort/Designability.lean
d11a358ceea0db8dc0954c44ff33eee5301f22129fe2bfa7d5c79e7a34dfffb7  RNA/AtMostTwoShort/Examples.lean
fe9f8e45db7bcc3b47795db31d3bb299d2bf4e2dc6661bfe1c99dcc36af0dae5  RNA/AtMostTwoShort/GlobalColoring.lean
ed3a68b268a4c82e12f45a6b733cda296ee0ee0902ec1ae62880b59489891fd0  RNA/AtMostTwoShort/Interface.lean
20511916e3b3a6d4be947113fbd664602c7a7a8f60dff99e37b1d0957acadc67  RNA/AtMostTwoShort/ResourceAllocations.lean
43ac425fb7b47dd094ac0c899cc949c3249cb81dea86820f8cc2e6ba727f2aaf  RNA/AtMostTwoShort/ResourceCertificate.lean
b4185bf73fe5679f825a76ff7ad803df4c0bded1c43e3cadd939e844aa0ef33e  RNA/AtMostTwoShort/ResourceRoot.lean
4c2423d4c791555d9338a40d2f2d9c89e79b866aa4fa91f8e6145d405634b073  RNA/AtMostTwoShort/ShortCount.lean
d742bac09e6a73ac2cfcefeb485044795efd0d2d410896f3aeadfc81d4af1103  RNA/AtMostTwoShort/SubtreeConstruction.lean
18be543996a716ea1be6589ad5cc160299b47cbe22adde4b62382209a9834254  RNA/AtMostTwoShort/TargetClass.lean
5c4c79ac68b5d7b8b8fa289f6ba433b5e824706314299207772ad6ff41f23907  RNA/AtMostTwoShort/Transfers.lean
38c655d2a8574bd25d8ea76da2acdd8a24def33bba6bbae0f0894ef88362f9d4  RNA/AtomicDesign.lean
cf88bca01fa5763a6e8578d2a59a059a8c389451fa1e10ed207ac08000870eba  RNA/AxiomAudit.lean
395e7f1c2481d5f142fcbbc9f76e0a93adf47bb74db3f9d8b1239e9c86194474  RNA/Color.lean
b39a7aabcfdfb28088e7432b9a6eb89cd2f9096de79153b54d7886ccf036b12e  RNA/Coloring.lean
0c6ec063e6dc9c27bd4c58e2edc783cd080a5a8e135c9da96604872a3070ab6f  RNA/Endpoint.lean
b1ef8775f5a97a62cbacd8cc75601659c089983cc455d6d4d8eb58d2a4c0db16  RNA/Examples.lean
a2925bcd57d859aac88fc376d5215d4646e4016787a786c9b15edcd9f1d5001e  RNA/FinalAxiomAudit.lean
b43a9767edc07fa1c7feb77c01640215d05c08a9bdb2349c34fbc105c8e23bcf  RNA/GlobalColoring.lean
028302a21280e6af0001b826f1e1b06f317699c477301408a9ce98ec5cbc9bd8  RNA/GlobalSequence.lean
03b69def8a4baefac27dde9d1ae4fde98dcf0cacc3e6345ef8d2392532dc7465  RNA/Helix.lean
2311caf8dbbc8ebf0059931e57e3e89d96fcff8dc882b90b55a5452c1b198d0b  RNA/HelixPartition.lean
be09e03ac01dc2a6ebc25dce6dba931e04f900553fbd8ada90f00934c05fb679  RNA/HelixSubtree.lean
1dc593f70e87dc8e370c84b5f28eee21e5ba9e35ae27c61c666a4aa198b22a68  RNA/HelixTransfer.lean
7dd7e69f1ea8e597bc0d26dddc9b4d7178d3e28e03d588b413e1df6ea8989dbb  RNA/HelixTransferBridge.lean
1fcca9ab46c7e78a288d82e77d76faf25cb14138253bb19a2e539d9818f935b1  RNA/IntervalTree.lean
fd2e5d696b1e9fb44f0958e0a879e2fc0b382431f4258c0faf3fa29b7e26d65a  RNA/LevelImbalance.lean
6cd6d4b9fc0f2e23c8d08c23afb90ba1cfd0760bd7e9c828d44232f45fd95bcd  RNA/LocalAllocations.lean
f8229cd2aac2d3ca1f523d0ee63e6b7fcc5bcbb82950df902f541ccca6d231f6  RNA/MatchingPartner.lean
c4a52dc3e0f9358b31ce451eb6b9a9584b0bbf31ebea000afdca2948b1e82220  RNA/Milestone2AxiomAudit.lean
1dd1d5cb3216303cd968754993850fe9d4927dceda58c58797ec6d21fac5eab9  RNA/Milestone2Examples.lean
4b067601c0f2949908246fb235dc9f46788e794ef999ab5ba7eda3834acc0050  RNA/Milestone3AxiomAudit.lean
6b10275e7b11ec29eeca6a9ed093cc1b5dcd0572c6ccb235b41ad82efbdc7fee  RNA/Milestone3Examples.lean
ed36b60fbb77d82be0dfdbd491be7966b3a5dbc980f0896eb0175415a734aafb  RNA/Milestone3Local.lean
2ad26c2507377cefd67e9c8861bedfa16379acdbd82cf9f44e1e4a8f7131747c  RNA/Milestone4AxiomAudit.lean
592c445ab9322bb33ee7368659e9ca2251945f4628aa41f591ebe2eb6458d138  RNA/Milestone4Examples.lean
ea98de0ddec29d17b45069e4b96abe9608371af391a6db3519c21986321e5422  RNA/Milestone5Examples.lean
79eecd6fb95fc33566dfbd81834c82a76c88dae17b9889c830be32e4b58a570a  RNA/Motifs.lean
e0414acc0d05c5e72510b32d2046c0272a8dda9a19a07021fcbf2b2d255bb645  RNA/NoTie.lean
c0be84c40370322e8d13ae50fb1c9057d4f222b03d907c2eedf98a7024e990d6  RNA/OneShortHelixDesignability.lean
e6639654296b1a3fe40d2fe557d4902c4c4d16ea7d544e888455b38b181e028f  RNA/PairedRestriction.lean
ef01cb510b8961af9f3bd1c244e431ee091a9f529d076e4281daf61786ff8ea9  RNA/PairingInventory.lean
8ffc57615e964ed85ef313d90ff3a715ca4fe9ed0f73610bebaf319c213d2e0b  RNA/PositionRole.lean
9d294e103b93593432bd69c4a6f41b8e67a9eba9610a521f3c8f44d094c88b35  RNA/PrefixBalance.lean
624c54982ae8ce6de9392bdc18c4047ce5729ba25dd2a116df9ecc363a13b906  RNA/Saturable.lean
a1438bafbc490414ce3aadf8284afed092c544428ee9cb34fc7a8f109a0a4d68  RNA/SaturatedUniqueness.lean
3dfa8b301ec02e6bfa3d2c8aab401852f6b5d4464e74a4a9a25a7717a3ce9e2b  RNA/SequenceAssignment.lean
65fda7ae255a3c23fa5fce1eee0f6e94f7213e4c2351a6ba0e7efb28f608c752  RNA/SequenceCertificate.lean
c1b7d3a091a0a2bc1b48f6f76f36fbe108532f70599d034c4202c612698ec90c  RNA/Statement.lean
ab3662a5730dd1d42f53859d43750a15e9b0edcb1e21e4a8ca0e3d5cda4d5451  RNA/Structure.lean
3c0b546a752abac2679a361a39b510ee41736e6bcde501e76dec86f6b40ba087  RNA/StructureOperations.lean
838914fd609b0755c3c932e9ff150d495354899bb1e41c2408e167abc6ca2db6  RNA/StructureTransport.lean
c642a847577bd63aeb0568310480186529b096bcd4aad462d12053f7d4f27bee  RNA/SubtreeColoring.lean
ae0ba071c310a782e84cbd7ca655b52bc42529057a41ca8d7dc0cfdc03cb2905  RNA/SubtreeConstruction.lean
422132fe80339c07f42183ac3d444a2b4663dd70a14ccb8f30b9418bb1d79c0d  RNA/TargetClass.lean
1fb6cffa20a4755080e9fd1542ad98daaa78c7e73f98701903ea6630c3f5ec30  RNA/TiedCompetitor.lean
b1f39e255767053c828ccd0654ef0f5c7950b8619abe6843e5571a871bba2406  RNA/Word.lean
```

## New-module SHA-256 values

```text
b5ae7b355ff7f7fad15a199c9d3ef69643c0dec803c6b02bb416002d1e0be9df  RNA/AtMostTwoShort/PublicationExamples.lean
f7013fde78e6b41bcb8134a60482bc2c181b3423beac341bac1cfc8d4c9af277  RNA/AtMostTwoShort/PublicationExamplesAxiomAudit.lean
```
