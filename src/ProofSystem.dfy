// ============================================================================
// LOGIC REPRESENTATION: Propositional Formulas
// ============================================================================
/**
 * Represents a propositional logic formula.
 * Supports atoms and standard logical connectives.
 */
datatype Formula =
  | Atom(name: string)                                    /* Atomic proposition (e.g., "p", "q") */
  | And(left: Formula, right: Formula)                    // Conjunction: φ ∧ ψ
  | Or(left: Formula, right: Formula)                     // Disjunction: φ ∨ ψ
  | Not(f: Formula)                                       // Negation: ¬φ
  | Implies(left: Formula, right: Formula)                // Implication: φ → ψ
  | Iff(left: Formula, right: Formula)                    // Biconditional: φ ↔ ψ 

// Justification for how a formula was derived in a proof.
datatype Justification = 
    | Assumption                                          /* Hypothesis / assumption             */
    | AndIntro(line1: nat, line2: nat)                    /* Conjunction Introduction            */
    | AndElimLeft(line: nat)                              /* And Elimination => Left expression  */
    | AndElimRight(line: nat)                             /* And Elimination => Right expression */
    | ImpliesElim(impliesLine: nat, antecedentLine: nat)  /* Implication Eliminations            */
    | OrIntroLeft(line: nat, right: Formula)              /* Disjunction Intro: from φ, infer φ ∨ ψ */
    | OrIntroRight(line: nat, left: Formula)              /* Disjunction Intro: from ψ, infer φ ∨ ψ */
    
// A proof contains a formula, and a justification.
datatype ProofLine = Line(formula: Formula, justification: Justification)

// Consecutive lines of proofs.
type Proof = seq<ProofLine>

/* p, q ⊢ p ∧ q
   Example proof:
   Line(Atom("p"), Assumption),
   Line(Atom("q"), Assumption),
   Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))  // Note: 0-indexed
*/

// Checks if the proof line at `lineIndex` is valid given all prior lines.
predicate ValidLine(proof: Proof, lineIndex: nat)
  requires lineIndex < |proof|
{
  var line := proof[lineIndex];
  match line.justification
  case Assumption => true  // Assumptions are always valid
  case AndIntro(i, j) =>
    (i < lineIndex &&
    j < lineIndex &&
    line.formula == And(proof[i].formula, proof[j].formula))  // Must combine two earlier formulas with ∧
  case ImpliesElim(i, j) =>
    (i < lineIndex && j < lineIndex &&
    match proof[i].formula
        case Implies(left, right) => proof[j].formula == left && line.formula == right  // Modus Ponens
        case _ => false)  // First line must be an implication
  case AndElimLeft(i) =>
    (i < lineIndex &&
    match proof[i].formula
        case And(left, right) => line.formula == left  // Extract left conjunct
        case _ => false)  // Source must be a conjunction
  case AndElimRight(i) =>
    (i < lineIndex &&
    match proof[i].formula
        case And(left, right) => line.formula == right  // Extract right conjunct
        case _ => false)  // Source must be a conjunction
  case OrIntroLeft(i, r) =>
    (i < lineIndex &&
    line.formula == Or(proof[i].formula, r))  // Introduce disjunction on the left: φ ⊢ φ ∨ ψ
  case OrIntroRight(i, l) =>
    (i < lineIndex &&
    line.formula == Or(l, proof[i].formula))  // Introduce disjunction on the right: ψ ⊢ φ ∨ ψ
  
}

// A proof is valid if every line is valid.
predicate ValidProof(proof: Proof)
{
    forall i :: 0 <= i < |proof| ==> ValidLine(proof, i)
}

// Functional version of ValidProof (for use in assertions/ensures).
function CheckProof(proof: Proof): bool
    ensures CheckProof(proof) == ValidProof(proof)
{
    forall i :: 0 <= i < |proof| ==> ValidLine(proof, i)
}

// The proof proves `goal` if it's valid and its last line is `goal`.
predicate Proves(proof: Proof, goal: Formula)
  requires |proof| > 0
{
  ValidProof(proof) && proof[|proof|-1].formula == goal
}




























// Basic correctness tests for proof validation.
method test()
{
  // CONJUNCTION ELIMINATION/INTRODUCTION
  var x: Proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))
  ];
  assert |x| == 3;
  assert(CheckProof(x) == true);

  var y: Proof := [Line(Atom("p"), Assumption), Line(Atom("q"), Assumption), Line(Atom("p"), AndIntro(0, 1))];
  assert |y| == 3;
  assert(ValidLine(y, 2) == false);
  assert(CheckProof(y) == false);

  var c: Proof := [Line(And(Atom("p"), Atom("q")), Assumption), Line(Atom("q"), AndElimRight(0))];
  assert |c| == 2;
  assert(CheckProof(c) == true);

  var d: Proof := [Line(And(Atom("p"), Atom("q")), Assumption), Line(Atom("p"), AndElimLeft(0))];
  assert |d| == 2;
  assert(CheckProof(d) == true);

  var e: Proof := [Line(And(Atom("p"), Atom("q")), Assumption), Line(Atom("q"), AndElimLeft(0))];
  assert |e| == 2;
  assert(ValidLine(e, 1) == false);
  assert(CheckProof(e) == false);

  // IMPLICATION ELIMINATION
  var z: Proof := [Line(Atom("p"), Assumption), Line(Implies(Atom("p"), Atom("q")), Assumption), Line(Atom("q"), ImpliesElim(1, 0))];
  assert |z| == 3;
  assert(CheckProof(z) == true);

  var a: Proof := [Line(Atom("p"), Assumption), Line(Implies(Atom("p"), Atom("q")), Assumption), Line(Atom("p"), ImpliesElim(1, 0))];
  assert |a| == 3;
  assert(ValidLine(a, 2) == false);
  assert(CheckProof(a) == false);
  assert(Proves(a, Atom("q")) == false);
}  









// ============================================================================
// TEST SUITE FOR ValidLine PREDICATE
// ============================================================================

// ----------------------------------------------------------------------------
// 1. ASSUMPTION TESTS
// ----------------------------------------------------------------------------

method TestAssumptionSimple()
{
  var proof := [Line(Atom("p"), Assumption)];
  assert ValidLine(proof, 0);
  assert CheckProof(proof);
}

method TestAssumptionComplex()
{
  var proof := [Line(And(Atom("p"), Atom("q")), Assumption)];
  assert ValidLine(proof, 0);
  assert CheckProof(proof);
}

method TestMultipleAssumptions()
{
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Atom("r"), Assumption)
  ];
  assert ValidLine(proof, 0);
  assert ValidLine(proof, 1);
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 2. AND INTRODUCTION TESTS
// ----------------------------------------------------------------------------

method TestAndIntroValid()
{
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}

method TestAndIntroReverseOrder()
{
  // Can combine in any order
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("q"), Atom("p")), AndIntro(1, 0))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}

method TestAndIntroWrongFormula()
{
  // Formula doesn't match the two lines being combined
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Atom("r"), AndIntro(0, 1))  // Should be And(p, q)
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}

method TestAndIntroWrongFormulaPartial()
{
  // One side is correct, other is wrong
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("r")), AndIntro(0, 1))  // Right side should be q
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}

method TestAndIntroFutureReference()
{
  // Referencing a line that comes after
  var proof := [
    Line(And(Atom("p"), Atom("q")), AndIntro(1, 2)),
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption)
  ];
  assert !ValidLine(proof, 0);
  assert !CheckProof(proof);
}

method TestAndIntroSelfReference()
{
  // Line cannot reference itself
  var proof := [
    Line(Atom("p"), Assumption),
    Line(And(Atom("p"), Atom("p")), AndIntro(1, 0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestAndIntroSameLineTwice()
{
  // Using same line for both sides is valid if formula matches
  var proof := [
    Line(Atom("p"), Assumption),
    Line(And(Atom("p"), Atom("p")), AndIntro(0, 0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestAndIntroNested()
{
  // Building nested And formulas
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Atom("r"), Assumption),
    Line(And(And(Atom("p"), Atom("q")), Atom("r")), AndIntro(2, 3))
  ];
  assert ValidLine(proof, 4);
  assert CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 3. AND ELIMINATION LEFT TESTS
// ----------------------------------------------------------------------------

method TestAndElimLeftValid()
{
  var proof := [
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), AndElimLeft(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestAndElimLeftWrongFormula()
{
  // Extracting wrong side (should be left, got right)
  var proof := [
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), AndElimLeft(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestAndElimLeftNotAnd()
{
  // Trying to eliminate from non-And formula
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("p"), AndElimLeft(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestAndElimLeftFromOr()
{
  // Trying to eliminate from Or (wrong operator)
  var proof := [
    Line(Or(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), AndElimLeft(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestAndElimLeftNested()
{
  // Eliminating from nested And
  var proof := [
    Line(And(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(And(Atom("p"), Atom("q")), AndElimLeft(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestAndElimLeftFutureReference()
{
  var proof := [
    Line(Atom("p"), AndElimLeft(1)),
    Line(And(Atom("p"), Atom("q")), Assumption)
  ];
  assert !ValidLine(proof, 0);
  assert !CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 4. AND ELIMINATION RIGHT TESTS
// ----------------------------------------------------------------------------

method TestAndElimRightValid()
{
  var proof := [
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), AndElimRight(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestAndElimRightWrongFormula()
{
  // Extracting wrong side (should be right, got left)
  var proof := [
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), AndElimRight(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestAndElimRightNotAnd()
{
  var proof := [
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), AndElimRight(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestAndElimRightNested()
{
  var proof := [
    Line(And(Atom("p"), And(Atom("q"), Atom("r"))), Assumption),
    Line(And(Atom("q"), Atom("r")), AndElimRight(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 5. IMPLIES ELIMINATION (MODUS PONENS) TESTS
// ----------------------------------------------------------------------------

method TestImpliesElimValid()
{
  var proof := [
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}

method TestImpliesElimReverseOrder()
{
  // Order of arguments matters: first is implication, second is antecedent
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), ImpliesElim(1, 0))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}

method TestImpliesElimWrongConsequent()
{
  // Result should be q, not p
  var proof := [
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), Assumption),
    Line(Atom("p"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}

method TestImpliesElimWrongAntecedent()
{
  // Second line doesn't match left side of implication
  var proof := [
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("r"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}

method TestImpliesElimNotImplication()
{
  // First line is not an implication
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}

method TestImpliesElimFromAnd()
{
  // Trying to use And as if it were Implies
  var proof := [
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}

method TestImpliesElimNested()
{
  // Implication with complex formulas
  var proof := [
    Line(Implies(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("r"), ImpliesElim(0, 1))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}

method TestImpliesElimChained()
{
  // Using result of one modus ponens in another
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), ImpliesElim(1, 0)),
    Line(Implies(Atom("q"), Atom("r")), Assumption),
    Line(Atom("r"), ImpliesElim(3, 2))
  ];
  assert ValidLine(proof, 4);
  assert CheckProof(proof);
}

method TestImpliesElimFutureReference()
{
  var proof := [
    Line(Atom("q"), ImpliesElim(1, 2)),
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), Assumption)
  ];
  assert !ValidLine(proof, 0);
  assert !CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 6. OR INTRODUCTION LEFT TESTS
// ----------------------------------------------------------------------------

method TestOrIntroLeftValid()
{
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), Atom("q")), OrIntroLeft(0, Atom("q")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestOrIntroLeftWrongLeft()
{
  // Left side of Or doesn't match referenced line
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Or(Atom("r"), Atom("q")), OrIntroLeft(0, Atom("q")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestOrIntroLeftWrongRight()
{
  // Right side of Or doesn't match provided formula
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), Atom("r")), OrIntroLeft(0, Atom("q")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestOrIntroLeftNotOr()
{
  // Result is not an Or formula
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("p"), OrIntroLeft(0, Atom("q")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestOrIntroLeftComplex()
{
  // Adding complex formula to right
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), And(Atom("q"), Atom("r"))), OrIntroLeft(0, And(Atom("q"), Atom("r"))))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestOrIntroLeftFromComplex()
{
  // Starting with complex formula on left
  var proof := [
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Or(And(Atom("p"), Atom("q")), Atom("r")), OrIntroLeft(0, Atom("r")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestOrIntroLeftFutureReference()
{
  var proof := [
    Line(Or(Atom("p"), Atom("q")), OrIntroLeft(1, Atom("q"))),
    Line(Atom("p"), Assumption)
  ];
  assert !ValidLine(proof, 0);
  assert !CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 7. OR INTRODUCTION RIGHT TESTS
// ----------------------------------------------------------------------------

method TestOrIntroRightValid()
{
  var proof := [
    Line(Atom("q"), Assumption),
    Line(Or(Atom("p"), Atom("q")), OrIntroRight(0, Atom("p")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestOrIntroRightWrongRight()
{
  // Right side of Or doesn't match referenced line
  var proof := [
    Line(Atom("q"), Assumption),
    Line(Or(Atom("p"), Atom("r")), OrIntroRight(0, Atom("p")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestOrIntroRightWrongLeft()
{
  // Left side of Or doesn't match provided formula
  var proof := [
    Line(Atom("q"), Assumption),
    Line(Or(Atom("r"), Atom("q")), OrIntroRight(0, Atom("p")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestOrIntroRightNotOr()
{
  var proof := [
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), OrIntroRight(0, Atom("p")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}

method TestOrIntroRightComplex()
{
  var proof := [
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Or(Atom("r"), And(Atom("p"), Atom("q"))), OrIntroRight(0, Atom("r")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

method TestOrIntroRightVsLeft()
{
  // Make sure Left and Right are different
  var proof1 := [
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), Atom("q")), OrIntroLeft(0, Atom("q")))
  ];
  var proof2 := [
    Line(Atom("p"), Assumption),
    Line(Or(Atom("q"), Atom("p")), OrIntroRight(0, Atom("q")))
  ];
  assert ValidLine(proof1, 1);
  assert ValidLine(proof2, 1);
  assert CheckProof(proof1);
  assert CheckProof(proof2);
}

// ----------------------------------------------------------------------------
// 8. COMBINED/INTEGRATION TESTS
// ----------------------------------------------------------------------------

method TestComplexProofValid()
{
  // (p ∧ q) → r, p, q ⊢ r
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Implies(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Atom("r"), ImpliesElim(2, 3))
  ];
  assert CheckProof(proof);
  assert Proves(proof, Atom("r"));
}

method TestComplexProofInvalid()
{
  // Same as above but wrong conclusion
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Implies(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(Atom("p"), ImpliesElim(3, 2))  // Should be r
  ];
  assert Proves(proof, Atom("r")) == false;
}

method TestBuildAndDestroy()
{
  // Build conjunction, then take it apart
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Atom("p"), AndElimLeft(2)),
    Line(Atom("q"), AndElimRight(2))
  ];
  assert CheckProof(proof);
}

method TestOrAndMix()
{
  // Mixing Or and And operations
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Or(Atom("p"), Atom("r")), OrIntroLeft(0, Atom("r"))),
    Line(And(Atom("q"), Or(Atom("p"), Atom("r"))), AndIntro(1, 2))
  ];
  assert CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 9. EDGE CASES AND BOUNDARY TESTS
// ----------------------------------------------------------------------------

method TestSingleLineProof()
{
  var proof := [Line(Atom("p"), Assumption)];
  assert CheckProof(proof);
  assert Proves(proof, Atom("p"));
}

method TestLongChain()
{
  // Long chain of implications
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), ImpliesElim(1, 0)),
    Line(Implies(Atom("q"), Atom("r")), Assumption),
    Line(Atom("r"), ImpliesElim(3, 2)),
    Line(Implies(Atom("r"), Atom("s")), Assumption),
    Line(Atom("s"), ImpliesElim(5, 4))
  ];
  assert CheckProof(proof);
  assert Proves(proof, Atom("s"));
}

method TestMaxIndexReference()
{
  // Reference the line immediately before
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))
  ];
  assert ValidLine(proof, 2);
}

method TestAllJustificationsInOneProof()
{
  // Use every type of justification
  var proof := [
    Line(Atom("a"), Assumption),                                    // 0: Assumption
    Line(Atom("b"), Assumption),                                    // 1: Assumption
    Line(And(Atom("a"), Atom("b")), AndIntro(0, 1)),               // 2: AndIntro
    Line(Atom("a"), AndElimLeft(2)),                               // 3: AndElimLeft
    Line(Atom("b"), AndElimRight(2)),                              // 4: AndElimRight
    Line(Or(Atom("a"), Atom("c")), OrIntroLeft(0, Atom("c"))),    // 5: OrIntroLeft
    Line(Or(Atom("d"), Atom("b")), OrIntroRight(1, Atom("d"))),   // 6: OrIntroRight
    Line(Implies(Atom("a"), Atom("e")), Assumption),               // 7: Assumption
    Line(Atom("e"), ImpliesElim(7, 0))                             // 8: ImpliesElim
  ];
  assert CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 10. STRESS TESTS
// ----------------------------------------------------------------------------

method TestDeeplyNestedFormulas()
{
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Atom("r"), Assumption),
    Line(And(And(Atom("p"), Atom("q")), Atom("r")), AndIntro(2, 3)),
    Line(Atom("s"), Assumption),
    Line(And(And(And(Atom("p"), Atom("q")), Atom("r")), Atom("s")), AndIntro(4, 5))
  ];
  assert CheckProof(proof);
}

method TestProvesWithWrongGoal()
{
  var proof := [
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption)
  ];
  assert !Proves(proof, Atom("r"));  // Proves q, not r
}

method TestProvesRequiresNonEmpty()
{
  // Proves requires |proof| > 0
  var emptyProof: Proof := [];
  // Cannot call Proves(emptyProof, Atom("p")) - precondition violation
}