# DWS Logic — Lean 4 Formalisation

Machine-verified formalisation of **Designable Worlds Semantics (DWS)**, an intuitionistic modal logic extending IK with a novel binary connective ▷ (*conduction*). The connective φ ▷ ψ captures the reasoning pattern "φ conduces to ψ": for every information extension at which φ holds, there exists a specification-preserving design move yielding ψ.

All proofs compile with **zero errors** and **no uses of `sorry`**.

This formalisation accompanies the paper:

> **Designable Worlds Semantics: An Intuitionistic Modal Logic for Design Reasoning**
> Luciano Floridi, Yale University

## Overview

DWS extends birelational Kripke semantics for intuitionistic modal logic (IK) with:

- **Bare frames** carrying a preorder ≤ (information growth) and an accessibility relation R (design moves), linked by a forward confluence condition (F6).
- **Enriched frames** adding affordance sets (Aff) and constraint sets (Con) with admissibility conditions (F7)–(F9).
- **A conduction connective** ▷ whose satisfaction clause (S8) requires: for all v ≥ w, if v ⊩ φ then there exists u with vRu, v ≤ u, and u ⊩ ψ. The conjunction of R-accessibility and ≤-extension in a single witness is the source of the connective's irreducibility.

## What Is Verified

The formalisation spans four namespaces: `Sem` (core semantics), `Enrichment` (enriched frames and admissibility), `Bisim` (bisimulation for the ▷-free fragment), and `IrredSep` (irreducibility separation via concrete countermodels).

### Core Semantics (Sem)

| Result | Paper Reference | Statement |
|--------|----------------|-----------|
| **Persistence** | Theorem 4.1 | Every formula satisfied at w remains satisfied at any ≤-successor v. Proved by structural induction on all connectives including ▷. |
| **Boundary Theorem I** | Proposition 5.4(i) | (φ ▷ ⊥) ↔ ¬φ — conduction to absurdity collapses to negation. |
| **Boundary Theorem II** | Proposition 5.4(ii) | ((φ ∨ ψ) ▷ χ) ↔ ((φ ▷ χ) ∧ (ψ ▷ χ)) — distribution over disjunction in the antecedent, both directions. |
| **Boundary Theorem III** | Proposition 5.4(iii) | (φ ▷ (ψ ∧ χ)) → ((φ ▷ ψ) ∧ (φ ▷ χ)) — distribution over conjunction in the consequent (one direction). |
| **C5** | Rule C5 | □(φ → ψ) → (φ ▷ ψ) under seriality (F10). Connects box modality to the conduction connective. |

### Enriched Frames (Enrichment)

| Result | Statement |
|--------|-----------|
| **C0 ↔ F9** | The joint constraint satisfiability condition C0 is definitionally equivalent to constraint self-satisfaction F9. |
| **Constraint at source** | F9 implies constraints hold at their state of origin. |
| **Constraint at successor** | F8 implies constraints propagate to R-successors. |
| **C3 (enriched)** | Under F7 and F9: if χ ∈ Con(w₀), then ((φ ∧ χ) ▷ ψ) → (φ ▷ ψ). Constraints can be shed from conditional antecedents. |
| **C3 (admissible)** | Same result derived from the compound Admissible condition. |

### Bisimulation Invariance (Bisim)

| Result | Paper Reference | Statement |
|--------|----------------|-----------|
| **Invariance** | Lemma 5.6 | For any IK-bisimulation Z and any ▷-free formula φ: if w₁ Z w₂ then M₁, w₁ ⊩ φ ↔ M₂, w₂ ⊩ φ. The conditional case is correctly excluded by the LIK predicate. |

### Irreducibility Separation (IrredSep)

| Result | Paper Reference | Statement |
|--------|----------------|-----------|
| **Z_bisim** | Theorem 5.8 | The total relation Z between two concrete two-world models MM and NN is a valid IK-bisimulation. |
| **M_w_cond_true** | Theorem 5.8 | φ ▷ ψ is satisfied at w in MM (where w ≤ u). |
| **N_wp_cond_false** | Theorem 5.8 | φ ▷ ψ is not satisfied at w' in NN (where w' ≰ u'). |
| **Irreducibility** | Theorem 5.8 | Together: ▷ is not invariant under IK-bisimulation, hence not definable in the IK fragment. |

### Conservative Extension

| Result | Paper Reference | Status |
|--------|----------------|--------|
| **Conservative extension** | Theorem 5.10 | ⚠️ Declared as axiom, not proved. The current statement is Valid.{u} φ ↔ Valid.{u} φ — a reflexive tautology that does not yet express the substantive claim. A genuine proof would require connecting the DWS semantics to a separate formalisation of standard IK validity. The paper should not cite this as a machine-verified result. |

## What Is Not Yet Verified in Lean

The following results from the paper are verified by hand (proof-checked in the companion report) but not yet formalised in Lean 4:

- Failure of excluded middle for ◇ (Theorem 4.2)
- Failure of □–◇ duality (Theorem 4.3)
- Constraint Blocks Action: □ψ → ¬◇¬ψ (Theorem 4.4)
- Possibility Defeats Necessity: ◇¬φ → ¬□φ (Theorem 4.5)
- Fragility of ◇ under pruning (Theorem 4.10)
- Rules C1, C2, C4
- Soundness of ▷-Right and ▷-Left (Theorems 7.2–7.3)
- Necessity of F10 for ▷-Right (Proposition 7.5)
- Barcan formula independence (Proposition 9.1)
- ▷ reduction axiom (Proposition 9.2)

## File Structure

This repository contains **File 1 of 4**. The remaining three files are yet to be verified. A comprehensive report will follow once all files have been processed.

## Requirements

- [Lean 4](https://leanprover.github.io/)
- [Mathlib](https://leanprover-community.github.io/)

To build:

```bash
lake build
