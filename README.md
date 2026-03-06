# DWS Logic — Lean 4 Formalisation

Machine-verified formalisation of Designable Worlds Semantics (DWS), an intuitionistic modal logic with a conditional operator (▷). All proofs compile with zero errors and no uses of sorry.

## What is verified

- Persistence of satisfaction under information growth
- Boundary theorems for the conditional operator
- C5: □(φ→ψ) → (φ ▷ ψ) under seriality
- Conservative extension over IK (Theorem 5.10)
- Bisimulation invariance for the ▷-free fragment
- Irreducibility of ▷ via concrete countermodels
- Enriched frame constraint reasoning (C3)

## Requirements

- Lean 4
- Mathlib

## Author

Luciano Floridi, Yale University
