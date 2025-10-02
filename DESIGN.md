# Design Documentation

## Architecture Overview

This document explains the design decisions behind the formal proof checker.

## Core Design Principles

### 1. Soundness Over Completeness

**Decision**: We prioritize soundness (no false proofs accepted) over completeness (all true statements provable).

**Rationale**: 
- A sound but incomplete system is still useful
- An unsound system is worthless for verification
- Missing rules can be added incrementally

### 2. Forward-Only References

**Decision**: Proof lines can only reference earlier lines (i < lineIndex).

**Rationale**:
- Ensures proofs are well-founded (no circular reasoning)
- Makes verification easier to reason about
- Matches natural proof construction (top-to-bottom)
- Prevents infinite loops in proof checking

```dafny
// Valid: Line 2 references lines 0 and 1
[
  Line(Atom("p"), Assumption),      // 0
  Line(Atom("q"), Assumption),      // 1
  Line(And(...), AndIntro(0, 1))    // 2 ✓
]

// Invalid: Line 0 references line 1
[
  Line(Atom("p"), AndElimLeft(1)),  // 0 ✗
  Line(And(...), Assumption)        // 1
]
```

### 3. Explicit Formula Construction

**Decision**: Each line explicitly states its formula; rules verify it matches expectations.

**Alternative**: Rules could construct formulas implicitly.

**Rationale**:
- More verbose but clearer for humans reading proofs
- Easier to debug when verification fails
- Matches how proofs are written on paper
- Separates concerns: construction vs. validation

### 4. Zero-Based Indexing

**Decision**: Proof lines indexed starting at 0.

**Rationale**:
- Matches programming conventions (Dafny sequences)
- Natural for CS audience
- Slightly less intuitive for math audience but acceptable

## Data Structure Design

### Formula ADT

```dafny
datatype Formula =
  | Atom(name: string)
  | And(left: Formula, right: Formula)
  | Or(left: Formula, right: Formula)
  | Not(f: Formula)
  | Implies(left: Formula, right: Formula)
  | Iff(left: Formula, right: Formula)
```

**Design Notes**:
- Algebraic data type provides pattern matching
- Recursive structure handles arbitrary nesting
- Immutable by default (functional programming style)

**Trade-offs**:
-  Type-safe construction
-  Exhaustive pattern matching
-  Easy to extend
-  No sharing of subformulas (could use hash-consing)
-  String-based atoms (could use interned symbols)

### Justification ADT

```dafny
datatype Justification = 
  | Assumption
  | AndIntro(line1: nat, line2: nat)
  | AndElimLeft(line: nat)
  | AndElimRight(line: nat)
  | ImpliesElim(impliesLine: nat, antecedentLine: nat)
  | OrIntroLeft(line: nat, right: Formula)
  | OrIntroRight(line: nat, right: Formula)
```

**Design Notes**:
- Each constructor represents a proof rule
- Natural numbers prevent negative indices
- OrIntro includes the "new" formula to add

**Alternative Considered**: 
```dafny
// Could have been:
| OrIntro(line: nat, newFormula: Formula, side: Side)
```
Rejected because separate Left/Right constructors are clearer.

### Proof as Sequence

```dafny
type Proof = seq<ProofLine>
```

**Rationale**:
- Sequences provide indexing (needed for line references)
- Preserves order (proofs are sequential)
- Built-in length operator
- Easy to iterate with forall

**Trade-offs**:
- Natural representation
- Efficient indexing
- Could be slow for very long proofs (not a concern in practice)

## Validation Architecture

### Two-Level Validation

```dafny
predicate ValidLine(proof: Proof, lineIndex: nat)
predicate ValidProof(proof: Proof)
```

**Rationale**:
- `ValidLine`: Validates single line in context
- `ValidProof`: Validates entire proof
- Separation allows testing individual rules
- `ValidProof` uses forall over `ValidLine`

### Pattern Matching for Rules

Each rule uses pattern matching on both:
1. The justification type
2. The formula structure being referenced

**Example** (ImpliesElim):
```dafny
case ImpliesElim(i, j) =>
  (i < lineIndex && j < lineIndex &&
  match proof[i].formula
    case Implies(left, right) => 
      proof[j].formula == left && line.formula == right
    case _ => false)
```

This double-match ensures:
- Referenced line exists and is earlier
- Referenced line has correct shape (Implies)
- Antecedent matches
- Consequent matches

### Preconditions

```dafny
predicate ValidLine(proof: Proof, lineIndex: nat)
  requires lineIndex < |proof|
```

**Rationale**:
- Prevents out-of-bounds access
- Verified statically by Dafny
- Caller must prove index is valid
- No runtime checks needed

## Rule Design Details

### And Introduction

**Rule**: From `P` and `Q`, derive `P ∧ Q`

**Implementation**:
```dafny
case AndIntro(i, j) =>
  (i < lineIndex &&
   j < lineIndex &&
   line.formula == And(proof[i].formula, proof[j].formula))
```

**Why not check formula types?**
- Not necessary! Any formulas can be conjoined
- Keeps rule simple
- Type checking done at construction level

### Implies Elimination (Modus Ponens)

**Rule**: From `P → Q` and `P`, derive `Q`

**Implementation**:
```dafny
case ImpliesElim(i, j) =>
  (i < lineIndex && j < lineIndex &&
   match proof[i].formula
     case Implies(left, right) => 
       proof[j].formula == left && line.formula == right
     case _ => false)
```

**Why match on proof[i]?**
- Must verify it's actually an implication
- Extract left and right parts
- Default case handles non-implications gracefully

### Or Introduction

**Design Question**: Why pass the "other" formula?

```dafny
case OrIntroLeft(i, r) =>
  (i < lineIndex &&
   line.formula == Or(proof[i].formula, r))
```

**Rationale**:
- Or introduction is unusual: creates disjunction from single disjunct
- Need to specify what to add
- Passing `r` makes it explicit
- More verbose but clearer intent

**Alternative**: Could infer from line.formula
- Would be implicit and harder to understand
- Current design is more explicit

## Verification Strategy

### Proves Predicate

```dafny
predicate Proves(proof: Proof, goal: Formula)
  requires |proof| > 0
{
  ValidProof(proof) && proof[|proof|-1].formula == goal
}
```

**Design Notes**:
- Requires non-empty proof (can't prove from nothing)
- Goal must be the last line
- Both validity AND goal-matching required

### CheckProof Function

```dafny
function CheckProof(proof: Proof): bool
  ensures CheckProof(proof) == ValidProof(proof)
{
  forall i :: 0 <= i < |proof| ==> ValidLine(proof, i)
}
```

**Why both CheckProof and ValidProof?**
- `ValidProof`: predicate (more abstract)
- `CheckProof`: function with postcondition
- Postcondition proves equivalence
- Demonstrates Dafny's verification capabilities

## Future Improvements

### Performance Optimizations

1. **Hash-consing formulas**: Share identical subformulas
2. **Proof caching**: Cache validation results
3. **Parallel validation**: Lines with no dependencies can be checked in parallel

### Feature Extensions

1. **Proof search**: Automatically construct proofs
2. **Proof minimization**: Remove redundant steps
3. **Better error messages**: Explain why line is invalid
4. **Proof transformations**: Convert between styles

### Theoretical Extensions

1. **Predicate logic**: Add ∀ and ∃
2. **Modal logic**: Add □ and ◇
3. **Proof terms**: Curry-Howard correspondence
4. **Proof extraction**: Generate executable code

## Testing Strategy

### Test Categories

1. **Positive tests**: Valid proofs should verify
2. **Negative tests**: Invalid proofs should fail
3. **Boundary tests**: Edge cases (empty, single line, etc.)
4. **Integration tests**: Complex multi-step proofs

### Coverage Goals

-  Every justification type
-  Every formula type
-  Every error condition
-  Combinations of rules

### Test Organization

Tests grouped by justification type for clarity:
- Easy to find relevant tests
- Easy to add new tests
- Clear what's covered

## Lessons Learned

### What Worked Well

1. **Algebraic data types**: Perfect for this domain
2. **Pattern matching**: Clean rule implementation
3. **Preconditions**: Caught bugs early
4. **Test-driven development**: Found edge cases

### What Was Challenging

1. **Or introduction design**: Took several iterations
2. **Index management**: Off-by-one errors
3. **Verification time**: Some proofs took multiple attempts
4. **Documentation**: Balancing detail vs. readability

### What I'd Do Differently

1. **Start with tests**: Should have written tests first
2. **More examples**: More real-world proof examples
3. **Better naming**: Some function names could be clearer
4. **Incremental development**: Add rules one at a time

## Conclusion

This design prioritizes:
- **Correctness**: Formal verification guarantees
- **Clarity**: Readable, well-documented code
- **Extensibility**: Easy to add new rules
- **Education**: Good learning resource

The result is a small but complete verified system that demonstrates formal methods in practice.
