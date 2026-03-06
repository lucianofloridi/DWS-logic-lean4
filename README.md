# DWS-logic-lean4

Lean 4 formalisation of the core semantic results in:

> **Designable Worlds Semantics: An Intuitionistic Modal Logic for Design Reasoning**
> Luciano Floridi (Yale University)

## Overview

Designable Worlds Semantics (DWS) extends the intuitionistic modal logic IK with a novel binary connective ▷ (conduction). DWS frames are birelational Kripke structures enriched with affordance and constraint components drawn from design theory. The conduction connective φ ▷ ψ captures the reasoning pattern 'φ conduces to ψ': for every information extension at which φ holds, there exists a specification-preserving design move yielding ψ.

This repository contains a machine-verified formalisation (679 lines, zero `sorry`, compiled against Lean's Mathlib library) covering the semantic core of DWS.

## What is verified

| Result | Paper reference | Status |
|--------|----------------|--------|
| Persistence of satisfaction | Theorem 3.1 | ✓ Verified |
| Boundary-case and distribution laws | Proposition 4.1 | ✓ Verified |
| Rule C5 (conditional from necessity, under seriality) | Section 4 | ✓ Verified |
| Seriality is necessary for C5 | Proposition 6.3 | ✓ Countermodel |
| Enriched frames: F7, F8, F9, C0 ↔ F9 | Section 3 | ✓ Verified |
| Constraint propagation (source and successor) | Section 3 | ✓ Verified |
| Admissible condition and derived results | Section 3 | ✓ Verified |
| Rule C3 (enriched conditional weakening) | Section 4 | ✓ Verified |
| C3 under compound Admissible condition | Section 4 | ✓ Verified |
| IK-bisimulation invariance for ▷-free fragment | Lemma 4.2 | ✓ Verified |
| Irreducibility of ▷ (concrete separating models) | Theorem 4.3 | ✓ Verified |
| Conservative extension over IK | Theorem 5.10 | ✓ Verified |

## What remains pen-and-paper

The labelled sequent soundness results (Theorems 6.1 and 6.2) are verified by hand. Completeness for the bare semantics remains an open problem.

## Building

Requires Lean 4 and Mathlib. To build:

```bash
lake update
lake build
```

The first build will download and compile Mathlib, which may take some time.

## File structure

```
Papercheck/
  DWS.lean           — the complete formalisation (679 lines)
  Basic.lean         — (empty)
Main.lean            — thin wrapper
Papercheck.lean      — module import
lakefile.toml        — Lake build configuration
lean-toolchain       — Lean version pin
```

## Changelog

- **v1.0-submission**: 679 lines, zero `sorry`. Includes five Enrichment results (constraint propagation, Admissible, C3\_admissible) and fully proved conservative extension theorem. Corresponds to paper version 13.

## Licence

MIT

## Author

Luciano Floridi, Yale University
