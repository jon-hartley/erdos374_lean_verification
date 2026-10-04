# Third-party code incorporated in this repository

Some project sources incorporate Lean code written by others. Copyright headers and license
statements are kept verbatim in the files. The Apache License 2.0 text is in
`LICENSES/Apache-2.0.txt`.

| Component | Where | Origin and license (as stated in the source) |
|---|---|---|
| PrimeNumberTheoremAnd (14 flattened modules, e.g. `Auxiliary`, `MellinCalculus`, `ZetaBounds`, `MediumPNT`) | `src/Erdos374_Update152.lean`, sections `Flat_PrimeNumberTheoremAnd_*`; shim `src/PrimeNumberTheoremAnd/ZetaBounds.lean` | PrimeNumberTheoremAnd project; Apache-2.0. Headers include Copyright (c) 2024 Michael Stoll. |
| Additive large sieve (`ImportedLargeSieve135`) | `src/Erdos374_Update152.lean`, §135A | https://github.com/ericlisg/erdos768-lean (`RequestProject/LargeSieve.lean`, parts of `LargeSieveMult.lean`); Apache-2.0, full text reproduced in the file. |
| Mathlib-derived snippet | `src/Erdos374_Update152.lean` | Copyright (c) 2022 Abby J. Goldberg; authors Abby J. Goldberg, Mario Carneiro, Heather Macbeth; Apache-2.0. |
| Riemann hypothesis for hyperelliptic curves over finite fields (`riemann_hypothesis_hec` and supporting lemmas) | `src/Erdos374_Update152.lean` (around `ExternalInputs149.coarseHyperellipticCount`) | Described in the source as the "Math Inc." theorem. **No license statement accompanies this code in the bundle; confirm its license before public release.** |
| Item-1 support files (`Item1Vmvt*.lean` and others with headers) | `src/` | Copyright (c) 2026 Jason Hickey (18 files) and Copyright (c) 2026 Salt contributors (`Item1VmvtPrimeCount.lean`); Apache-2.0. |

Mathlib and its dependencies are not vendored. Lake fetches them at the pinned revisions
(Apache-2.0).
