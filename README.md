# Katanamu (కతనం)

**Katanamu** (కతనం, meaning *Reason* or *Cause* in Mēlimi Telugu) is a minimal 
**natural-deduction proof checker** written in **Dafny** for propositional logic.  

It represents logical formulas (`Atom`, `And`, `Or`, `Not`, `Implies`, `Iff`) 
and validates proofs line by line using explicit justifications 
(`Assumption`, `AndIntro`, `AndElim`, `ImpliesElim`, `OrIntro`).  

`Katanamu` ensures **no forward references** and provides predicates to check 
validity (`ValidProof`), functionally assert correctness (`CheckProof`), and 
verify that a proof derives its intended conclusion (`Proves`).

## Quick Start

```bash
# Verify the system
dafny verify src/ProofSystem.dfy

# Run tests
dafny verify src/Tests.dfy
```

---

## Example

Prove **modus ponens**: Given `P → Q` and `P`, derive `Q`

```dafny
var proof := [
  Line(Atom("P"), Assumption),
  Line(Implies(Atom("P"), Atom("Q")), Assumption),
  Line(Atom("Q"), ImpliesElim(1, 0))
];

assert CheckProof(proof);  // Verified!
```

[More examples →](./examples/)

---

## Features

**Logical Operators**  
∧ (And) · ∨ (Or) · → (Implies) · ¬ (Not) · ↔ (Iff)

**Inference Rules**
- Introduction and elimination for ∧, ∨, →
- Assumption handling
- Modus ponens

**Guarantees**
- 70+ verified test cases
- No runtime errors possible
- Sound inference rules

---

## Architecture

```
Formula         → Logical expressions (atoms + connectives)
Justification   → Proof rules (how each line is derived)
ValidLine       → Verifies individual proof steps
ValidProof      → Ensures entire proof is correct
```

**Key Design**: Lines can only reference *earlier* lines, preventing circular reasoning and ensuring well-founded proofs.

See [`DESIGN.md`](./docs/DESIGN.md) for detailed architecture.

---

## Project Structure

```
src/
  ProofSystem.dfy    # Core system
  Tests.dfy          # Test suite
examples/
  basic_proofs.dfy   # Example proofs
docs/
  DESIGN.md          # Design decisions
  TUTORIAL.md        # Getting started
```

---

## Technical Highlights

- **Formal verification** - Dafny proves code correctness mathematically
- **Type safety** - Invalid proof structures impossible to construct
- **Inductive reasoning** - Each line builds on prior lines only
- **Preconditions** - Index bounds checked at compile-time

---

## Future Work

- Subproofs
- Predicate logic (∀, ∃)
- Natural deduction for disjunction elimination, negation, implication introduction, etc. (all of which rely on subproofs).
- Proof search and optimization
- Interactive proof assistant interface
  
---

## Built With

[Dafny](https://dafny.org/) - Verification-aware programming language

---

## Author

**Your Name**  
[GitHub](https://github.com/PuneetPuli)

---

## License

MIT - see [LICENSE](LICENSE)

---

*Built to explore formal methods and program verification*
