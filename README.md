# Katanamu (కతనము)

> A minimal natural-deduction proof checker in Dafny

[![Dafny](https://img.shields.io/badge/Dafny-4.0+-blue.svg)](https://dafny.org/)
![Formal Methods](https://img.shields.io/badge/Formal%20Methods-Verified-brightgreen)
![Logic](https://img.shields.io/badge/Logic-Natural%20Deduction-orange)
![Tests](https://img.shields.io/badge/Tests-100%2B-green)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

## Overview

**Katanamu** (కతనం, *reason* or *cause* in Mēlimi Telugu) is a formally verified proof checker for propositional logic. It validates natural deduction proofs line-by-line, ensuring each inference step is sound.

**Current scope:** Full propositional logic with conjunction, disjunction, implication, and negation. The system supports both direct inference rules and subproof-based reasoning for natural deduction.

---

## Project Stats

- **100+ verified test cases** covering all implemented rules
- **~1000 lines of code** (concise and readable with detailed comments)
- **100% coverage** of all inference rules
- **<15 second** verification time

---

## Why Formal Verification?

Traditional testing: "Does this work for these 100 inputs?"
Formal verification: "Does this work for ALL possible inputs?"

Katanamu guarantees that **invalid proofs cannot be constructed**, providing stronger correctness guarantees than any amount of testing.

---

## Quick Start

```bash
# Verify the system
dafny verify ProofSystem.dfy

# Run tests
dafny verify basic_proofs.dfy
```

---

## Example Proofs

### Modus Ponens
Given `P → Q` and `P`, derive `Q`

```dafny
var proof := [
  Line(Atom("P"), Assumption),
  Line(Implies(Atom("P"), Atom("Q")), Assumption),
  Line(Atom("Q"), ImpliesElim(1, 0))
];

assert CheckProof(proof);  // Verified!
```

### Implication Introduction
Prove `A → (A ∨ B)`

```dafny
var proof := [
  Subproof(
    Atom("A"),
    [
      Line(Atom("A"), Assumption),
      Line(Or(Atom("A"), Atom("B")), OrIntroLeft(0, Atom("B")))
    ]
  ),
  Line(Implies(Atom("A"), Or(Atom("A"), Atom("B"))), ImpliesIntro(0))
];

assert Proves(proof, Implies(Atom("A"), Or(Atom("A"), Atom("B"))));
```

### Disjunction Elimination
Prove `A ∨ (B ∨ C) ⊢ (A ∨ B) ∨ C`

```dafny
var proof := [
  Line(Or(Atom("A"), Or(Atom("B"), Atom("C"))), Assumption),
  Subproof(
    Atom("A"),
    [
      Line(Atom("A"), Assumption),
      Line(Or(Atom("A"), Atom("B")), OrIntroLeft(0, Atom("B"))),
      Line(Or(Or(Atom("A"), Atom("B")), Atom("C")), OrIntroLeft(1, Atom("C")))
    ]
  ),
  Subproof(
    Or(Atom("B"), Atom("C")),
    [/* nested case analysis */]
  ),
  Line(Or(Or(Atom("A"), Atom("B")), Atom("C")), DisjunctionElimination(0, 1, 2))
];
```

[More examples →](./examples/)

---

## Implemented Features

**Logical Operators**  
∧ (And) · ∨ (Or) · → (Implies) · ¬ (Not)  
*Note: Iff (↔) is defined but lacks inference rules*

**Inference Rules**

*Basic Rules*
- `Assumption` - Introduce hypotheses

*Conjunction*
- `AndIntro` - From A and B, derive A ∧ B
- `AndElimLeft` / `AndElimRight` - Extract left/right from A ∧ B

*Disjunction*
- `OrIntroLeft` / `OrIntroRight` - Add disjunct to create A ∨ B
- `DisjunctionElimination` - Case analysis on A ∨ B with subproofs

*Implication*
- `ImpliesElim` - Modus ponens: From A → B and A, derive B
- `ImpliesIntro` - Discharge subproof to create implication

*Negation*
- `NegationIntroduction` - Proof by contradiction: derive ¬A from assuming A leads to contradiction
- `NegationElimination` - Double negation: from ¬¬A, derive A

**Subproofs**
- Self-contained proof blocks with local assumptions
- First-class support for hypothetical reasoning
- Validated assumption matching and recursive proof checking

**What's Missing**
- Biconditional introduction/elimination (↔)
- Classical logic axioms (Law of Excluded Middle, etc.)
- Predicate logic (∀, ∃)

**Verification**
- 100+ test cases covering all implemented rules
- Sound inference (invalid proofs are impossible)
- No runtime errors
- Comprehensive edge case testing

---

## Architecture

```
Formula         → Logical expressions (atoms + connectives)
Justification   → Proof rules (how each line is derived)
ProofLine       → Either a Line or a Subproof
ValidLine       → Verifies individual proof steps (with recursive subproof validation)
ValidProof      → Ensures entire proof is correct
Proves          → Validates proof achieves goal formula
```

**Key constraints:**
- Lines can only reference *earlier* lines (prevents circular reasoning)
- Subproofs are self-contained (no external line references)
- First line of subproof must match its declared assumption

See [`DESIGN.md`](./DESIGN.md) for detailed architecture.

---

## Project Structure

```
fitch_style_parser.dfy    # Core proof system
tests.dfy                 # Comprehensive test suite (100+ tests)
examples/
  basic_proofs.dfy        # Example proofs
docs/
  DESIGN.md               # Design decisions
```

---

## Technical Highlights

- **Formal verification** - Dafny mathematically proves correctness
- **Type safety** - Invalid proof structures impossible to construct
- **Subproof mechanism** - Full support for hypothetical reasoning
- **Forward-only references** - Each line builds on prior lines only
- **Recursive validation** - Subproofs validated with same rigor as main proofs
- **Contradiction detection** - Bidirectional formula matching for negation rules
- **Compile-time bounds checking** - Index safety via preconditions

---

## Testing Philosophy

The test suite follows a comprehensive pattern:
- **Basic valid cases** - Standard usage of each rule
- **Complex formulas** - Nested and compound expressions
- **Invalid cases** - Wrong formulas, types, and structures
- **Index errors** - Future references, out-of-bounds, type mismatches
- **Edge cases** - Empty proofs, self-references, deeply nested structures
- **Integration tests** - Rules working together in realistic proofs

Every inference rule has 10-15 dedicated test cases ensuring correctness.

---

## Future Work

**Core Extensions**
- Biconditional introduction/elimination
- Classical axioms (excluded middle, double negation as axiom)
- Proof optimization and simplification

**Advanced Features**
- Predicate logic (∀, ∃)
- Proof search and automated theorem proving
- Interactive proof assistant interface
- Proof visualization and export

**Tooling**
- VSCode extension for proof development
- Web-based proof checker
- Proof library and standard theorems

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
