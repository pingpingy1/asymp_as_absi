# Lean Formalization

This directory contains the Lean 4 mechanization of the formal framework introduced in the paper.

The mechanization serves as a validation of the framework’s formal soundness rather than a full proof development. It defines the semantic domains and orderings used in the paper, and partially formalizes the abstraction–concretization interface.

---

## Structure

- **[`Domain.lean`](LeanProof/Domain.lean)**  
  Defines the three semantic domains:
  - *Denotational domain* `Dd`  
  - *Concrete domain* `Dc`  
  - *Abstract domain* `Da`  
  together with their respective ordering relations (`⊑d`, `⊑c`, `⊑a`) and proofs that each forms a preorder/partial order (reflexive, antisymmetric, transitive).

- **[`Galois.lean`](LeanProof/Galois.lean)**  
  Defines the abstraction (`α`) and concretization (`γ`) functions and states the Galois connection between the concrete and abstract domains.  
  *(Proof currently under development.)*

- **`Semantics.lean`**  
  Placeholder for the compositional definition of the concrete and abstract semantics and the proof of correctness for assertion checking.  
  *(To be implemented.)*

## Notes

- The implementation uses **Mathlib** for analytic constructs (`Sup`, `Inf`, `limsup`, etc.).  
- The formalization is **noncomputable** in places (e.g., `α`) and focuses on definitional coherence.  
- Currently verified components include all ordering proofs and the type-correctness of domain definitions.

## Goals

This Lean development aims to:
1. Validate the internal consistency of the abstract interpretation framework.
2. Provide a foundation for future mechanized proofs of:
   - the **Galois connection** between `α` and `γ`, and  
   - the **soundness of assertion checking**.
