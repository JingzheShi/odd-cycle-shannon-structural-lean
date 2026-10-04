# Attribution, licensing and selected sources

This is a curated public release, not a copy of the private research history.
The code and mathematical data in this repository are distributed under
Apache-2.0; see `LICENSE` and the retained per-file notices. New release prose
and the paper are also made available under Apache-2.0. Bibliographic citations
do not redistribute the cited articles. No publisher PDFs are included.

## Inherited mathematics and source

- **Pjotr Buys, Sven Polak, Jeroen Zuiddam (BPZ)**: strong-power and capacity
  definitions, actual cycle graphs and finite base data, rich port systems,
  layered realizations, substitutions, terminal codes and flattening. Selected
  `lean/ShannonBounds/` files retain their copyright and Apache-2.0 headers.
  Pinned source: `spectra-research/shannon-capacity-lean`,
  `aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65`.
- **Yu Gao**: recursive private-pair/transversal gadget product. Its paper
  routing here corresponds to upstream `liftRPS S (flip T)`.
- **Ravi Tandon**: heterogeneous auxiliary sets and the inherited C7 side
  constructions/exchanges. Mathematical source: arXiv:2608.30273v1 and the
  Apache-2.0 `tandonravi/C7-Shannon-Capacity-Heterogeneous-Recursion` materials.
  The selected recipe/base JSON files are mathematical construction inputs;
  the formal semantic and count proofs are in `C7Improvement/`, not assumptions
  that those input profiles are realizable.
- **Matthew Protti**: guarded typed-cell method and literal C13 base cells.
  Pinned source: `matthewprotti/c11-shannon-capacity-lower-bound` v0.5.0,
  `dfaef37e60e55c55b1744d9badd1f26c5364c7d5`, Apache-2.0. The original header
  in `TypedBase.lean` is retained; the generic typed method is not claimed
  as invented by this release.
- **Griffin Long**: C13 recursion DAG and generic DAG helpers. Pinned source:
  `griffinwork40/shannon-capacity-c15-c19` v1.1,
  `a06e1a19278852350eb912c585adf0888fb54b91`, Apache-2.0. `PublicLong.lean`,
  `DagTail.lean` and `DagCode3.lean` retain the original Long/agent-afk
  contribution notices. The curated Long modules relocate imports/namespaces
  to `ExplorationC13FrontierR03` and remove display-only diagnostics; the
  mathematical schedule is the selected original.
- **Oleksii Stavriianov**: chosen prior C7 certificate, release 1.0.3,
  `577c73e967531a77c8adde2bb71fd99656435c4c`, DOI 10.5281/zenodo.22728595.
  Only the mathematical integer and bibliographic reference are included,
  not third-party repository code or an unlicensed article.

Mathlib is an external Apache-2.0 dependency pinned to
`905b95818eb32af7874a58b427f50c1711a5e96c`; Lean is pinned to 4.32.2.

## Frozen project inputs and contribution boundary

- The complete C7 actual-code chain in `C7Improvement/` is the accepted
  300-dimensional construction, including all four actual side counts.
  Its capacity source was completed at `df04ec5ff28c95fc126968ac659fd705db6dd78c`.
- The C13 typed certificate was frozen at
  `9d41754c16ae462f4b6a6ee0ff29ffc5653a2560`. Its contribution is a concrete
  Protti-on-Long combination, not invention of guarded cells.
- The local C13 structural sources were frozen at
  `ea265ae96991dffbd9590758564931ddc951932c`. The exact small-slack local
  region, physical bridge and explicit balanced witness are new to this
  project. General isoperimetry, Ferrers compression and voltage-fiber
  representation are classical; no worldwide-priority claim is made.
- The classical C7 illustration was frozen at
  `16dcf870cab6e138742182a0c14d1c15c60f3db6`.
  Its geometry and whole-block realization use existing principles, and it
  provides no stronger capacity bound or new general method.

The paper's principal author labels are exactly `GPT-6.1-Sol, GPT-6-Astra`,
identifying AI systems. Jingzhe Shi is credited in the shared author footnote
and acknowledgements for providing tokens and some of the vibemath prompts and
guidance used in this work. No affiliation or contact is asserted.
Selected historical audit reports are included as accepted evidence, not as
newly rerun computations. New publication-time validation compiles only the
aggregate target against exact-source accepted artifacts, as stated in the
README and validation receipt.
