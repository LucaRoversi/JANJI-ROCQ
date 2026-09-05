# JANJI-ROCQ

This repository contains the official reference implementation in Rocq that
supports the correctness of the results in the paper *Hardening MCP-Enabled
Agentic Workflows: a Type-and-Effect System for Trace Safety* (Aldinucci,
Bracciali, Colonnelli, Medic, Mulone, Roversi, and Santimaria). The code is
released under the MIT/Apache-2.0 license to maximize reproducibility and
scientific reuse.

## Requirements

The minimum requirements for compiling the project are:

- Coq Proof Assistant 8.17.1, with `coqc`, `coq_makefile`, and `coqchk`
  available on `PATH`.
- GNU Make, available as `make` on `PATH`.

Only the Coq standard library is used. No external Coq libraries, `opam`
packages, Dune, or Docker are required.

From the repository root, compile with:

```console
make
```

Optionally, verify the compiled development with Coq's kernel checker:

```console
make check
```

## Theory guide

### Reference paper

The reference document is `GianluigiFerrari_tribute_final.pdf` in the project root.
Page references in the `.v` comments are physical pages of that 39-page PDF.

The Rocq development is more detailed than the paper. Some source files encode
definitions, rules, examples, and theorems that are stated explicitly in the
paper. Other files, or substantial parts of mixed files, provide finite
representations, decomposition lemmas, preservation lemmas, and induction
infrastructure required for the complete mechanization.

### File-by-file classification

#### [`Prelude.v`](theories/Prelude.v)

**Classification:** Mainly technical.

It chooses natural numbers as executable representatives of the paper's
abstract name classes and supplies elementary list and finite-set lemmas. The
name classes themselves correspond to Section 5.2 and Appendix C, Table C.2.

#### [`Syntax.v`](theories/Syntax.v)

**Classification:** Mainly paper-facing, with technical representation details.

It encodes the paper's capabilities, value types, primitive effects, traces,
static and dynamic environments, tool and workflow descriptors,
model-mediated actions, and call side conditions from Sections 5 and 6.

#### [`Trace.v`](theories/Trace.v)

**Classification:** Mixed.

Its main relations correspond directly to the paper's availability, freshness,
proposal, effect order, dependency, source closure, and protocol-stage notions
in Sections 5.3 and 5.4. Its closing list lemmas are technical support for later
preservation proofs.

#### [`Policy.v`](theories/Policy.v)

**Classification:** Mainly paper-facing, with technical proof lemmas.

It encodes the query family, terminating oracle interface, prefix
admissibility, exact commitment safety, and source-sensitive flow safety from
Sections 5.4 and 6.2. Prefix-decomposition and extraction lemmas provide
mechanization infrastructure.

#### [`Typing.v`](theories/Typing.v)

**Classification:** Mainly paper-facing.

The typing constructors implement `T-Obs`, `T-Derive`, `T-Propose`, `T-Commit`,
`T-Call`, and `T-Seq` from Section 6.1. Exact environment extension,
result-shape bindings, and source checks make premises that are compact in the
paper explicit enough for Rocq.

#### [`Semantics.v`](theories/Semantics.v)

**Classification:** Mainly paper-facing, with technical interfaces.

It encodes the runtime abstraction and lifting, configurations, boundary
labels, rules `R-Observe` through `R-Internal`, reachability, and boundary
fidelity from Sections 7.1-7.3. Binding projections and constructor-specific
lemmas are mainly proof support.

#### [`FilesystemOracle.v`](theories/FilesystemOracle.v)

**Classification:** Mainly paper-facing.

It is the executable version of Appendix A, including `O-Read`, `O-Propose`,
`O-Commit`, `O-Call`, `O-Act`, and `O-Flow`. Boolean case analysis and denial
lemmas are technical evidence for totality and decidability.

#### [`Examples.v`](theories/Examples.v)

**Classification:** Paper-facing but deliberately smaller than the displayed
examples.

It isolates the proof-critical parts of `OK-TRACE`, `NOT-OK-TRACE`, and
`NOT-OK-FLOW` from Section 4 and Appendix B. Numeric identifiers and test
oracles are executable instantiations rather than additional theory.

#### [`Safety.v`](theories/Safety.v)

**Classification:** Mainly technical and intermediate.

It packages core admissibility, provenance, commitment, and flow consequences
for the unstrengthened reachability relation. These results reflect Section
6.2, but this file is not by itself the final Trace Safety theorem of the paper.

#### [`one_step_agentic_provenance_and_authority_confinement.v`](theories/one_step_agentic_provenance_and_authority_confinement.v)

**Classification:** Mixed, with a major direct correspondence.

Groups 1-9 mechanize Definitions 19-26, Propositions 1-2, and Theorem 1 in
Section 7.4.1. The file also contains extensive auxiliary records, inversion
results, exact-production lemmas, and preservation proofs that the paper
summarizes in its proof-justification paragraph.

#### [`trace_safety.v`](theories/trace_safety.v)

**Classification:** Mixed, with a major direct correspondence.

It mechanizes administrative closure, the persistent trace invariant,
certified finite reachability, and the final Trace Safety theorem corresponding
to Definitions 28-30 and Theorem 2 in Section 7.4.2. Reconstruction, base-case,
and induction lemmas are the technical structure needed for the full Rocq
proof.

### Suggested reading order

For the closest route through the paper-facing material, read
[`Syntax.v`](theories/Syntax.v), [`Trace.v`](theories/Trace.v),
[`Policy.v`](theories/Policy.v), [`Typing.v`](theories/Typing.v),
[`Semantics.v`](theories/Semantics.v),
[`FilesystemOracle.v`](theories/FilesystemOracle.v), and
[`Examples.v`](theories/Examples.v). Then read the numbered groups in
[`one_step_agentic_provenance_and_authority_confinement.v`](theories/one_step_agentic_provenance_and_authority_confinement.v)
and the final statement in [`trace_safety.v`](theories/trace_safety.v). Consult
[`Prelude.v`](theories/Prelude.v), [`Safety.v`](theories/Safety.v), and the
auxiliary lemmas in the mixed files when following the complete machine-checked
proof.
