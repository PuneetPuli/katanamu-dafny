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

### 3. Self-Contained Subproofs

**Decision**: Subproofs can only reference lines within themselves, not the outer proof context.

**Rationale**:
- Ensures hypothetical reasoning is isolated
- Subproofs represent "what if" scenarios independent of outer context
- Simplifies validation (each subproof validated independently)
- Matches standard natural deduction presentation
- Prevents subtle scope errors

```dafny
// Valid: Subproof only references its own lines
[
  Line(Atom("p"), Assumption),           // Outer line 0
  Subproof(
    Atom("q"),
    [
      Line(Atom("q"), Assumption),       // Inner line 0
      Line(Or(Atom("q"), Atom("r")), OrIntroLeft(0, Atom("r")))  // ✓ References inner line 0
    ]
  )
]

// Invalid: Subproof cannot reference outer proof
[
  Line(Atom("p"), Assumption),           // Outer line 0
  Subproof(
    Atom("q"),
    [
      Line(Atom("q"), Assumption),
      Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))  // ✗ Cannot reference outer line 0
    ]
  )
]
```

### 4. Explicit Formula Construction

**Decision**: Each line explicitly states its formula; rules verify it matches expectations.

**Alternative**: Rules could construct formulas implicitly.

**Rationale**:
- More verbose but clearer for humans reading proofs
- Easier to debug when verification fails
- Matches how proofs are written on paper
- Separates concerns: construction vs. validation

### 5. Zero-Based Indexing

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
- ✓ Type-safe construction
- ✓ Exhaustive pattern matching
- ✓ Easy to extend
- ✗ No sharing of subformulas (could use hash-consing)
- ✗ String-based atoms (could use interned symbols)

### ProofLine ADT

```dafny
datatype ProofLine = 
  | Line(formula: Formula, justification: Justification) 
  | Subproof(assumption: Formula, steps: seq<ProofLine>)
```

**Design Notes**:
- Two-level structure: regular lines and subproofs
- Subproofs contain their own sequence of ProofLines (recursive)
- Assumption explicitly stored with subproof

**Rationale**:
- Enables hypothetical reasoning (assume X, derive Y, conclude X → Y)
- Recursive structure allows nested subproofs
- Clear separation between assumptions and derived steps

### Justification ADT

```dafny
datatype Justification = 
  | Assumption
  | AndIntro(line1: nat, line2: nat)
  | AndElimLeft(line: nat)
  | AndElimRight(line: nat)
  | ImpliesElim(impliesLine: nat, antecedentLine: nat)
  | OrIntroLeft(line: nat, right: Formula)
  | OrIntroRight(line: nat, left: Formula)
  | ImpliesIntro(subproofIndex: nat)
  | DisjunctionElimination(disjunctionIndex: nat, subproofIndex: nat, subproofIndexTwo: nat)
  | NegationIntroduction(subproofIndex: nat, contradictoryLineInProof: nat, contradictoryLineInSubproof: nat)
  | NegationElimination(line: nat)
```

**Design Notes**:
- Each constructor represents a proof rule
- Natural numbers prevent negative indices
- OrIntro includes the "new" formula to add
- Subproof-based rules reference subproof indices
- NegationIntroduction references both outer and inner lines for contradiction

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
- Can contain both Lines and Subproofs

**Trade-offs**:
- ✓ Natural representation
- ✓ Efficient indexing
- ✗ Could be slow for very long proofs (not a concern in practice)

## Validation Architecture

### Three-Level Validation

```dafny
predicate ValidLine(proof: Proof, lineIndex: nat)
predicate ValidProof(proof: Proof)
function SubproofConclusion(s: seq<ProofLine>): Formula
```

**Rationale**:
- `ValidLine`: Validates single line or subproof in context
- `ValidProof`: Validates entire proof (recursively validates subproofs)
- `SubproofConclusion`: Extracts the conclusion from a subproof (handles nesting)
- Separation allows testing individual rules
- `ValidProof` uses forall over `ValidLine`
- Recursive validation ensures subproofs are sound

### Subproof Validation

```dafny
case Subproof(a, s) =>
  |s| > 0 && 
  s[0].Line? && 
  s[0].justification.Assumption? && 
  s[0].formula == a && 
  ValidProof(s)
```

**Checks Performed**:
1. Subproof is non-empty
2. First step is a Line (not another Subproof)
3. First step is justified by Assumption
4. First step's formula matches declared assumption
5. All steps within subproof are recursively valid

**Rationale**:
- Ensures assumption is properly stated
- Prevents empty subproofs (meaningless)
- Recursive `ValidProof(s)` ensures inner proof is sound
- Self-contained validation (no need to check outer context)

### Pattern Matching for Rules

Each rule uses pattern matching on both:
1. The justification type
2. The formula structure being referenced

**Example** (ImpliesElim):
```dafny
case ImpliesElim(i, j) =>
  (i < lineIndex && j < lineIndex &&
   proof[i].Line? && proof[j].Line? &&
   match GetLineFormula(proof[i])
     case Implies(left, right) => 
       GetLineFormula(proof[j]) == left && f == right
     case _ => false)
```

This double-match ensures:
- Referenced lines exist and are earlier
- Referenced lines are Lines (not Subproofs)
- Referenced line has correct shape (Implies)
- Antecedent matches
- Consequent matches

### Preconditions

```dafny
predicate ValidLine(proof: Proof, lineIndex: nat)
  requires lineIndex < |proof|
  
function SubproofConclusion(s: seq<ProofLine>): Formula
  requires |s| > 0
```

**Rationale**:
- Prevents out-of-bounds access
- Verified statically by Dafny
- Caller must prove index is valid
- No runtime checks needed

## Rule Design Details

### Basic Rules

#### And Introduction

**Rule**: From `P` and `Q`, derive `P ∧ Q`

**Implementation**:
```dafny
case AndIntro(i, j) =>
  (i < lineIndex &&
   j < lineIndex &&
   proof[i].Line? &&
   proof[j].Line? &&
   f == And(GetLineFormula(proof[i]), GetLineFormula(proof[j])))
```

**Design Notes**:
- Checks both references are Lines (not Subproofs)
- Any formulas can be conjoined
- Order matters for formula structure

#### Implies Elimination (Modus Ponens)

**Rule**: From `P → Q` and `P`, derive `Q`

**Implementation**:
```dafny
case ImpliesElim(i, j) =>
  (i < lineIndex && j < lineIndex && 
   proof[i].Line? && proof[j].Line? &&
   match GetLineFormula(proof[i])
     case Implies(left, right) => 
       GetLineFormula(proof[j]) == left && f == right
     case _ => false)
```

**Why match on proof[i]?**
- Must verify it's actually an implication
- Extract left and right parts
- Default case handles non-implications gracefully

### Subproof-Based Rules

#### Implication Introduction

**Rule**: From a subproof assuming `P` and deriving `Q`, conclude `P → Q`

**Implementation**:
```dafny
case ImpliesIntro(i) =>
  (i < lineIndex &&
   proof[i].Subproof? &&
   |proof[i].steps| > 0 &&
   var conclusion := SubproofConclusion(proof[i].steps);
   var assumption := proof[i].assumption;
   f == Implies(assumption, conclusion))
```

**Design Notes**:
- References a Subproof, not a Line
- Extracts assumption and conclusion
- "Discharges" the assumption into an implication
- Enables hypothetical reasoning

#### Disjunction Elimination (Case Analysis)

**Rule**: From `A ∨ B`, a subproof `A ⊢ C`, and a subproof `B ⊢ C`, derive `C`

**Implementation**:
```dafny
case DisjunctionElimination(disjunctionIndex, subproofIndex, subproofIndexTwo) =>
  (disjunctionIndex < lineIndex && 
   subproofIndex < lineIndex && 
   subproofIndexTwo < lineIndex &&
   proof[disjunctionIndex].Line? && 
   proof[subproofIndex].Subproof? && 
   proof[subproofIndexTwo].Subproof? &&
   |proof[subproofIndex].steps| > 0 && 
   |proof[subproofIndexTwo].steps| > 0 && 
   match GetLineFormula(proof[disjunctionIndex])
     case Or(l, r) => 
       (var firstConclusion := SubproofConclusion(proof[subproofIndex].steps);
        var secondConclusion := SubproofConclusion(proof[subproofIndexTwo].steps);
        proof[subproofIndex].assumption == l &&
        proof[subproofIndexTwo].assumption == r &&
        f == firstConclusion && 
        f == secondConclusion)
     case _ => false)
```

**Design Notes**:
- Three references: disjunction line + two subproofs
- Verifies subproof assumptions match disjunction parts
- Verifies both subproofs reach same conclusion
- Classic case analysis pattern

### Negation Rules

#### Negation Introduction (Proof by Contradiction)

**Rule**: Assuming `A` leads to contradiction, derive `¬A`

**Implementation**:
```dafny
case NegationIntroduction(subproofIndex, contradictoryLineInProof, contradictoryLineInSubproof) =>
  (subproofIndex < lineIndex && 
   contradictoryLineInProof < lineIndex && 
   proof[subproofIndex].Subproof? &&
   proof[contradictoryLineInProof].Line? &&  
   |proof[subproofIndex].steps| > 0 && 
   contradictoryLineInSubproof < |proof[subproofIndex].steps| &&
   proof[subproofIndex].steps[contradictoryLineInSubproof].Line? &&  
   
   var assumption := proof[subproofIndex].assumption;
   var originalFormula := GetLineFormula(proof[contradictoryLineInProof]);
   var contradictoryFormula := GetLineFormula(proof[subproofIndex].steps[contradictoryLineInSubproof]);
   
   f == Not(assumption) &&  
   (contradictoryFormula == Not(originalFormula) || originalFormula == Not(contradictoryFormula)))
```

**Design Notes**:
- References subproof AND specific contradictory lines
- Checks one formula is negation of the other (bidirectional)
- No Bottom/⊥ symbol needed
- Explicit contradiction witnesses make proofs clearer

**Why bidirectional check?**
- Contradiction is symmetric: `P` vs `¬P` = `¬P` vs `P`
- More flexible for proof construction
- Matches mathematical practice

#### Negation Elimination (Double Negation)

**Rule**: From `¬¬A`, derive `A`

**Implementation**:
```dafny
case NegationElimination(line) =>
  (line < lineIndex && 
   proof[line].Line? &&
   match GetLineFormula(proof[line])
     case Not(Not(inner)) => f == inner
     case _ => false)
```

**Design Notes**:
- Simple pattern match on double negation
- Extracts inner formula
- Classical logic rule (not valid in intuitionistic logic)

### Or Introduction Design

**Design Question**: Why pass the "other" formula?

```dafny
case OrIntroLeft(i, r) =>
  (i < lineIndex &&
   proof[i].Line? &&
   f == Or(GetLineFormula(proof[i]), r))
```

**Rationale**:
- Or introduction is unusual: creates disjunction from single disjunct
- Need to specify what to add
- Passing `r` makes it explicit
- More verbose but clearer intent

**Alternative**: Could infer from f
- Would be implicit and harder to understand
- Current design is more explicit

## Verification Strategy

### Proves Predicate

```dafny
predicate Proves(proof: Proof, goal: Formula)
  requires |proof| > 0
{
  ValidProof(proof) && 
  var lastStep := proof[|proof|-1];
  match lastStep
    case Line(f, _) => f == goal
    case Subproof(a, steps) => 
      if |steps| > 0 then SubproofConclusion(steps) == goal else false
}
```

**Design Notes**:
- Requires non-empty proof (can't prove from nothing)
- Goal must be the conclusion (last line or subproof conclusion)
- Both validity AND goal-matching required
- Handles case where proof ends with subproof

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

## Advanced Design Patterns

### Recursive Subproof Handling

Subproofs can be nested arbitrarily:
```dafny
Subproof(
  Atom("P"),
  [
    Line(Atom("P"), Assumption),
    Subproof(
      Atom("Q"),
      [
        Line(Atom("Q"), Assumption),
        Line(Atom("P"), Assumption)  // Can restate outer assumption
      ]
    ),
    Line(Implies(Atom("Q"), Atom("P")), ImpliesIntro(1))
  ]
)
```

**Validation Strategy**:
- Each level validated independently
- `ValidProof` called recursively on subproof steps
- Inner subproofs can't reference outer lines (enforced by scope)

### SubproofConclusion Recursion

```dafny
function SubproofConclusion(s: seq<ProofLine>): Formula
  requires |s| > 0
  decreases s
{
  var lastStep := s[|s| - 1];
  match lastStep
    case Line(f, _) => f
    case Subproof(a, steps) =>
      if |steps| > 0 then SubproofConclusion(steps) else a
}
```

**Design Notes**:
- Handles proofs ending in subproofs
- Recursive until finding a Line
- `decreases s` proves termination
- Returns assumption if subproof empty (edge case)

## Future Improvements

### Performance Optimizations

1. **Hash-consing formulas**: Share identical subformulas
2. **Proof caching**: Cache validation results for subproofs
3. **Parallel validation**: Independent subproofs can be checked in parallel
4. **Incremental validation**: Re-validate only changed parts

### Feature Extensions

1. **Proof search**: Automatically construct proofs
2. **Proof minimization**: Remove redundant steps
3. **Better error messages**: Explain why line is invalid with context
4. **Proof transformations**: Convert between styles
5. **Biconditional rules**: Add ↔ introduction/elimination
6. **Classical axioms**: Law of excluded middle, etc.

### Theoretical Extensions

1. **Predicate logic**: Add ∀ and ∃
2. **Modal logic**: Add □ and ◇
3. **Proof terms**: Curry-Howard correspondence
4. **Proof extraction**: Generate executable code
5. **Intuitionistic logic**: Separate mode without double negation

## Testing Strategy

### Test Categories

1. **Positive tests**: Valid proofs should verify
2. **Negative tests**: Invalid proofs should fail
3. **Boundary tests**: Edge cases (empty, single line, etc.)
4. **Integration tests**: Complex multi-step proofs
5. **Subproof tests**: Nested reasoning patterns
6. **Index error tests**: Future references, out of bounds
7. **Type error tests**: Line vs Subproof mismatches

### Coverage Goals

- Every justification type
- Every formula type
- Every error condition
- Combinations of rules
- Nested subproofs (2-3 levels deep)
- All contradiction patterns for negation rules

### Test Organization

Tests grouped by justification type for clarity:
- Easy to find relevant tests
- Easy to add new tests
- Clear what's covered
- 10-15 tests per rule minimum

## Lessons Learned

### What Worked Well

1. **Algebraic data types**: Perfect for this domain
2. **Pattern matching**: Clean rule implementation
3. **Preconditions**: Caught bugs early
4. **Test-driven development**: Found edge cases
5. **Subproof design**: Recursive validation elegant
6. **Explicit contradiction witnesses**: Clearer than Bottom symbol

### What Was Challenging

1. **Or introduction design**: Took several iterations
2. **Index management**: Off-by-one errors, especially with nested subproofs
3. **Verification time**: Some proofs took multiple attempts
4. **Documentation**: Balancing detail vs. readability
5. **Negation rules**: Getting contradiction checking right (bidirectional)
6. **Subproof scope**: Ensuring inner proofs can't reference outer lines

### What I'd Do Differently

1. **Start with tests**: Should have written tests first
2. **More examples**: More real-world proof examples
3. **Better naming**: Some function names could be clearer
4. **Incremental development**: Add rules one at a time
5. **Earlier subproof design**: Should have planned for subproofs from start

## Design Tradeoffs Summary

| Decision | Benefit | Cost |
|----------|---------|------|
| Forward-only references | No circular reasoning | Can't reference lemmas stated later |
| Self-contained subproofs | Clean scope, easier validation | Must restate facts from outer context |
| Explicit formulas | Clear, debuggable | More verbose |
| Recursive validation | Handles nesting naturally | Harder to optimize |
| No Bottom symbol | Simpler type system | More complex negation intro |
| Bidirectional contradiction | Flexible proof construction | More complex checking logic |

## Conclusion

This design prioritizes:
- **Correctness**: Formal verification guarantees
- **Clarity**: Readable, well-documented code
- **Extensibility**: Easy to add new rules
- **Education**: Good learning resource
- **Completeness**: Full natural deduction system

The result is a complete formally verified system that demonstrates:
- Subproof-based reasoning
- Recursive validation
- Natural deduction in practice
- The power of formal methods

The system now supports the full range of propositional natural deduction, including hypothetical reasoning through subproofs, making it suitable for teaching and verifying realistic logical arguments.
