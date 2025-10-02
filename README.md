# Katanamu (కతనం)

> A minimal natural-deduction proof checker in Dafny

[![Dafny](https://img.shields.io/badge/Dafny-4.0+-blue.svg)](https://dafny.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

## Overview

**Katanamu** (కతనం, *reason* or *cause* in Mēlimi Telugu) is a formally verified proof checker for propositional logic. It validates natural deduction proofs line-by-line, ensuring each inference step is sound.

**Current scope:** Basic propositional logic with conjunction, disjunction, and implication. Advanced features like subproofs, negation rules, and implication introduction are planned for future releases.

---
## Project Stats

- **70+ verified test cases** covering all implemented rules
- **~500 lines of code** (concise and readable)
- **100% coverage** of implemented inference rules
- **<5 second** verification time
---
## Why Formal Verification?

Traditional testing: "Does this work for these 100 inputs?"
Formal verification: "Does this work for ALL possible inputs?"

This project mathematically proves that invalid proofs cannot be constructed, providing stronger guarantees than any amount of testing
---
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

## Implemented Features

**Logical Operators**  
∧ (And) · ∨ (Or) · → (Implies)  
*Note: Not (¬) and Iff (↔) are defined but lack inference rules*

**Inference Rules**
- `Assumption` - Introduce hypotheses
- `AndIntro` / `AndElimLeft` / `AndElimRight` - Conjunction rules
- `OrIntroLeft` / `OrIntroRight` - Disjunction introduction
- `ImpliesElim` - Modus ponens

**What's Missing**
- Disjunction elimination (case analysis)
- Negation introduction/elimination
- Implication introduction (requires subproofs)
- Biconditional rules

**Verification**
- 70+ test cases covering all implemented rules
- Sound inference (invalid proofs are impossible)
- No runtime errors

---

## Architecture

```
Formula         → Logical expressions (atoms + connectives)
Justification   → Proof rules (how each line is derived)
ValidLine       → Verifies individual proof steps
ValidProof      → Ensures entire proof is correct
```

**Key constraint:** Lines can only reference *earlier* lines, preventing circular reasoning.

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
```

---

## Technical Highlights

- **Formal verification** - Dafny mathematically proves correctness
- **Type safety** - Invalid proof structures impossible to construct  
- **Forward-only references** - Each line builds on prior lines only
- **Compile-time bounds checking** - Index safety via preconditions

---

## Future Work

**Core Extensions**
- Subproof mechanism (required for most remaining rules)
- Negation introduction/elimination
- Implication introduction
- Disjunction elimination
- Biconditional rules

**Advanced Features**
- Predicate logic (∀, ∃)
- Proof search and optimization
- Interactive proof assistant interface

---

## Built With

[Dafny](https://dafny.org/) - Verification-aware programming language

---

## Author

**Puneet Puli**  
[GitHub](https://github.com/PuneetPuli)

---

## License

MIT - see [LICENSE](LICENSE)

---

*Built to explore formal methods and program verification*
