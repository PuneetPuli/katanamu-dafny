// =============================================================
// Fitch-Style Parser (Dafny) — Plain-English Guide
// -------------------------------------------------------------
// This file defines a parser for a Fitch-style natural-deduction
// proof language. The comments added here are written to be clear,
// practical, and non-jargony. They explain *what* each piece does
// and *why it exists*, without using heavy formal-methods lingo.
// 
// How to read these comments:
//  • Blocks above definitions explain their role at a high level.
//  • Spec lines like `requires`, `ensures`, and loop `invariant`s
//    are translated into everyday language right next to them.
//  • Control-flow markers (like `match`/`case`) have quick hints
//    about what branch is being handled.
// 
// =============================================================

// ============================================================================
// LOGIC REPRESENTATION: Propositional Formulas
// ============================================================================
/**
 * Represents a propositional logic formula.
 * Supports atoms and standard logical connectives.
 */

// --- datatype `Formula` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
datatype Formula =
  | Atom(name: string)                            // Atomic proposition (e.g., "p", "q")
  | And(left: Formula, right: Formula)            // Conjunction: φ ∧ ψ
  | Or(left: Formula, right: Formula)             // Disjunction: φ ∨ ψ
  | Not(f: Formula)                               // Negation: ¬φ
  | Implies(left: Formula, right: Formula)        // Implication: φ → ψ
  | Iff(left: Formula, right: Formula)            // Biconditional: φ ↔ ψ

// Justification for how a formula was derived in a proof.

// --- datatype `Justification` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
datatype Justification = 
    | Assumption                                          /* Hypothesis / assumption             */
    | AndIntro(line1: nat, line2: nat)                    /* Conjunction Introduction            */
    | AndElimLeft(line: nat)                              /* And Elimination => Left expression  */
    | AndElimRight(line: nat)                             /* And Elimination => Right expression */
    | ImpliesElim(impliesLine: nat, antecedentLine: nat)  /* Implication Eliminations            */
    | OrIntroLeft(line: nat, right: Formula)              /* Disjunction Intro: from φ, infer φ ∨ ψ */
    | OrIntroRight(line: nat, left: Formula)              /* Disjunction Intro: from ψ, infer φ ∨ ψ */
    | ImpliesIntro(subproofIndex: nat)
    | DisjunctionElimination(disjunctionIndex: nat, subproofIndex: nat, subproofIndexTwo: nat)
    | NegationIntroduction(subproofIndex: nat, contradictoryLineInProof: nat, contradictoryLineInSubproof: nat)
    | NegationElimination(line1: nat)
    
// A proof contains a formula, and a justification or a subproof which contains an assumption, and a list of proofs.

// --- datatype `ProofLine` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
datatype ProofLine = Line(formula: Formula, justification: Justification) | Subproof(assumption: Formula, steps: seq<ProofLine>)

// Consecutive lines of proofs.
type Proof = seq<ProofLine>

/*
   Example proof:
   Line(Atom("p"), Assumption),
   Line(Atom("q"), Assumption),
   Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))  // Note: 0-indexed
*/


// --- function `GetLineFormula` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
function GetLineFormula(step: ProofLine): Formula
  requires step.Line?    // needs to be true before this runs: step.Line?
{
  step.formula 
}


// --- function `SubproofConclusion` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
function SubproofConclusion(s: seq<ProofLine>): Formula
  requires |s| > 0  // needs to be true before this runs: |s| > 0
  decreases s  // this gets smaller each loop (helps prove it ends): s
{
  var lastStep := s[|s| - 1];  // Define a new local name to hold a value
  match lastStep  // Look at the shape/kind of the thing and branch on it
    case Line(f, _) => f  // Handle this specific pattern/case
    case Subproof(a, steps) =>  // Handle this specific pattern/case
      if |steps| > 0 then SubproofConclusion(steps) else a  // If this condition holds, do the following block
}
// A proof is valid if every line is valid.

// --- predicate `ValidProof` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
predicate ValidProof(proof: Proof)
{
    forall i :: 0 <= i < |proof| ==> ValidLine(proof, i)
}

// Functional version of ValidProof (for use in assertions/ensures).

// --- function `CheckProof` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
function CheckProof(proof: Proof): bool
    ensures CheckProof(proof) == ValidProof(proof)  // promises to be true when this finishes: CheckProof(proof) equals ValidProof(proof)
{
    forall i :: 0 <= i < |proof| ==> ValidLine(proof, i)
}


// --- predicate `Proves` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
predicate Proves(proof: Proof, goal: Formula)
  requires |proof| > 0  // needs to be true before this runs: |proof| > 0
{
  ValidProof(proof) && 
  var lastStep := proof[|proof|-1];  // Define a new local name to hold a value
  match lastStep  // Look at the shape/kind of the thing and branch on it
    case Line(f, _) => f == goal  // Handle this specific pattern/case
    case Subproof(a, steps) =>   if |steps| > 0 then SubproofConclusion(steps) == goal else false  // Handle this specific pattern/case
}

// Checks if the proof line at `lineIndex` is valid given all prior lines.

// --- predicate `ValidLine` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
predicate ValidLine(proof: Proof, lineIndex: nat)
  requires lineIndex < |proof|  // needs to be true before this runs: lineIndex < |proof|
{
  var line := proof[lineIndex];  // Define a new local name to hold a value
  match line  // Look at the shape/kind of the thing and branch on it
  case Line(f, j) =>  // Handle this specific pattern/case
    (match j
       case Assumption => true    // Handle this specific pattern/case
       case AndIntro(i, j) =>  // Handle this specific pattern/case
        (i < lineIndex && 
        j < lineIndex &&
        proof[i].Line? &&  
        proof[j].Line? &&  
        f == And(GetLineFormula(proof[i]), GetLineFormula(proof[j])))  
       case ImpliesElim(i, j) =>  // Handle this specific pattern/case
        (i < lineIndex && j < lineIndex && proof[i].Line? && proof[j].Line? &&
          match GetLineFormula(proof[i])  // Look at the shape/kind of the thing and branch on it
            case Implies(left, right) => GetLineFormula(proof[j]) == left && f == right  // Handle this specific pattern/case
            case _ => false)  // Handle this specific pattern/case
       case AndElimLeft(i) =>  // Handle this specific pattern/case
          (i < lineIndex && proof[i].Line? &&
            match GetLineFormula(proof[i])  // Look at the shape/kind of the thing and branch on it
              case And(left, right) => f == left    // Handle this specific pattern/case
              case _ => false)  // Handle this specific pattern/case
       case AndElimRight(i) =>  // Handle this specific pattern/case
          (i < lineIndex && proof[i].Line? &&
            match GetLineFormula(proof[i])  // Look at the shape/kind of the thing and branch on it
              case And(left, right) => f == right    // Handle this specific pattern/case
              case _ => false)  // Handle this specific pattern/case
       case OrIntroLeft(i, r) =>  // Handle this specific pattern/case
          (i < lineIndex && proof[i].Line? &&
          f == Or(GetLineFormula(proof[i]), r))
       case OrIntroRight(i, l) =>  // Handle this specific pattern/case
          (i < lineIndex && proof[i].Line? &&
          f == Or(l, GetLineFormula(proof[i])))
       case ImpliesIntro(i) =>  // Handle this specific pattern/case
        (i < lineIndex &&
        proof[i].Subproof? &&
        |proof[i].steps| > 0 &&
        var conclusion := SubproofConclusion(proof[i].steps);  // Define a new local name to hold a value
        var assumption := proof[i].assumption;  // Define a new local name to hold a value
        f == Implies(assumption, conclusion))
       case DisjunctionElimination(disjunctionIndex, subproofIndex, subproofIndexTwo) =>  // Handle this specific pattern/case
        (disjunctionIndex < lineIndex && 
        subproofIndex < lineIndex && 
        subproofIndexTwo < lineIndex &&
        proof[disjunctionIndex].Line? && 
        proof[subproofIndex].Subproof? && 
        proof[subproofIndexTwo].Subproof? &&
        |proof[subproofIndex].steps| > 0 && 
        |proof[subproofIndexTwo].steps| > 0 && 
          match GetLineFormula(proof[disjunctionIndex])  // Look at the shape/kind of the thing and branch on it
            case Or(l, r) =>   // Handle this specific pattern/case
              (var firstSubproofConclusion := SubproofConclusion(proof[subproofIndex].steps);
              var secondSubProofConclusion := SubproofConclusion(proof[subproofIndexTwo].steps);  // Define a new local name to hold a value
              proof[subproofIndex].assumption == l &&
              proof[subproofIndexTwo].assumption == r &&
              f == firstSubproofConclusion && 
              f == secondSubProofConclusion)
          case _ => false  // Handle this specific pattern/case
        )
       case NegationIntroduction(subproofIndex, contradictoryLineInProof, contradictoryLineInSubproof) =>  // Handle this specific pattern/case
        (subproofIndex < lineIndex && 
        contradictoryLineInProof < lineIndex && 
        proof[subproofIndex].Subproof? &&
        proof[contradictoryLineInProof].Line? &&  
        |proof[subproofIndex].steps| > 0 && 
        contradictoryLineInSubproof < |proof[subproofIndex].steps| &&
        proof[subproofIndex].steps[contradictoryLineInSubproof].Line? &&  
   
        var assumption := proof[subproofIndex].assumption;  // Define a new local name to hold a value
        var originalFormula := GetLineFormula(proof[contradictoryLineInProof]);  // Define a new local name to hold a value
        var contradictoryFormula := GetLineFormula(proof[subproofIndex].steps[contradictoryLineInSubproof]);  // Define a new local name to hold a value
   
        f == Not(assumption) &&  (contradictoryFormula == Not(originalFormula) || originalFormula == Not(contradictoryFormula))
        )
       case NegationElimination(line) =>  // Handle this specific pattern/case
        (line < lineIndex && proof[line].Line? &&
         match GetLineFormula(proof[line])  // Look at the shape/kind of the thing and branch on it
          case Not(Not(inner)) => f == inner  // Handle this specific pattern/case
          case _ => false)  // Handle this specific pattern/case
    )
  case Subproof(a, s) =>  // Handle this specific pattern/case
    |s| > 0 && s[0].Line? && s[0].justification.Assumption? && s[0].formula == a && ValidProof(s)
}


// --- method `TestNegationElimination` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestNegationElimination()
{
  // Prove: ¬¬(A ∧ B) ⊢ A ∧ B
  
  var proof: Proof := [  // Define a new local name to hold a value
    // Given: ¬¬(A ∧ B)
    Line(Not(Not(And(Atom("A"), Atom("B")))), Assumption),  // Line 0: ¬¬(A ∧ B)
    
    // Apply negation elimination to remove double negation
    Line(And(Atom("A"), Atom("B")), NegationElimination(0))  // Line 1: A ∧ B
  ];
  
  var goal := And(Atom("A"), Atom("B"));  // Define a new local name to hold a value
  
  assert |proof| > 0;
  assert ValidProof(proof);
  assert Proves(proof, goal);
  
  print "Negation elimination test (¬¬(A ∧ B) ⊢ A ∧ B) passed!\n";
}


// --- method `TestSimpleImplication` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestSimpleImplication()
{
  // Prove: A → A
  
  var proof: Proof := [  // Define a new local name to hold a value
    // Subproof: Assume A, conclude A
    Subproof(
      Atom("A"),  // assumption: A
      [
        Line(Atom("A"), Assumption)  // 0s: A (we just restate what we assumed)
      ]
    ),  // Subproof at index 0
    
    // Use implication introduction to discharge the subproof
    Line(Implies(Atom("A"), Atom("A")), ImpliesIntro(0))  // Line 1: A → A
  ];
  
  var goal := Implies(Atom("A"), Atom("A"));  // Define a new local name to hold a value
  
  assert |proof| > 0;
  assert ValidProof(proof);
  assert Proves(proof, goal);
  
  print "Simple implication (A → A) test passed!\n";
}


// --- method `TestNegationIntroduction` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestNegationIntroduction()
{
  // Prove: ¬(A ∨ ¬A) ⊢ ¬A
  // Strategy: Assume ¬(A ∨ ¬A), then assume A and derive A ∨ ¬A (contradiction!)
  
  var proof: Proof := [  // Define a new local name to hold a value
    // Given: ¬(A ∨ ¬A)
    Line(Not(Or(Atom("A"), Not(Atom("A")))), Assumption),  // Line 0
    
    // Subproof: Assume A, derive contradiction
    Subproof(
      Atom("A"),  // assumption: A
      [
        Line(Atom("A"), Assumption),                                           // 0s: A
        Line(Or(Atom("A"), Not(Atom("A"))), OrIntroLeft(0, Not(Atom("A"))))  // 1s: A ∨ ¬A
      ]
    ),  // Subproof at index 1
    
    // Conclude ¬A using negation introduction
    // We have ¬(A ∨ ¬A) at line 0, and (A ∨ ¬A) at subproof line 1
    Line(Not(Atom("A")), NegationIntroduction(1, 0, 1))  // Line 2: ¬A
  ];
  
  var goal := Not(Atom("A"));  // Define a new local name to hold a value
  
  assert |proof| > 0;
  assert ValidProof(proof);
  assert Proves(proof, goal);
  
  //"Negation introduction test (¬(A ∨ ¬A) ⊢ ¬A) passed!
}


// --- method `TestDisjunctionElimination` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestDisjunctionElimination()
{
  // Prove: A ∨ (B ∨ C) ⊢ (A ∨ B) ∨ C
  
  var proof: Proof := [  // Define a new local name to hold a value
    // Given: A ∨ (B ∨ C)
    Line(Or(Atom("A"), Or(Atom("B"), Atom("C"))), Assumption),  // Line 0
    
    // Subproof 1: Assume A, derive (A ∨ B) ∨ C
    Subproof(
      Atom("A"),  // assumption: A
      [
        Line(Atom("A"), Assumption),                                    // 0s: A
        Line(Or(Atom("A"), Atom("B")), OrIntroLeft(0, Atom("B"))),     // 1s: A ∨ B
        Line(Or(Or(Atom("A"), Atom("B")), Atom("C")),                  // 2s: (A ∨ B) ∨ C
             OrIntroLeft(1, Atom("C")))
      ]
    ),  // Subproof at index 1
    
    // Subproof 2: Assume B ∨ C, derive (A ∨ B) ∨ C
    Subproof(
      Or(Atom("B"), Atom("C")),  // assumption: B ∨ C
      [
        Line(Or(Atom("B"), Atom("C")), Assumption),  // 0s: B ∨ C
        
        // Inner subproof 2a: Assume B, derive (A ∨ B) ∨ C
        Subproof(
          Atom("B"),  // assumption: B
          [
            Line(Atom("B"), Assumption),                                  // 0ss: B
            Line(Or(Atom("A"), Atom("B")), OrIntroRight(0, Atom("A"))),  // 1ss: A ∨ B
            Line(Or(Or(Atom("A"), Atom("B")), Atom("C")),                // 2ss: (A ∨ B) ∨ C
                 OrIntroLeft(1, Atom("C")))
          ]
        ),  // Inner subproof at index 1s
        
        // Inner subproof 2b: Assume C, derive (A ∨ B) ∨ C
        Subproof(
          Atom("C"),  // assumption: C
          [
            Line(Atom("C"), Assumption),                                  // 0ss: C
            Line(Or(Or(Atom("A"), Atom("B")), Atom("C")),                // 1ss: (A ∨ B) ∨ C
                 OrIntroRight(0, Or(Atom("A"), Atom("B"))))
          ]
        ),  // Inner subproof at index 2s
        
        // Eliminate B ∨ C using the two inner subproofs
        Line(Or(Or(Atom("A"), Atom("B")), Atom("C")),                    // 3s: (A ∨ B) ∨ C
             DisjunctionElimination(0, 1, 2))
      ]
    ),  // Subproof at index 2
    
    // Finally, eliminate A ∨ (B ∨ C) using subproofs 1 and 2
    Line(Or(Or(Atom("A"), Atom("B")), Atom("C")),
         DisjunctionElimination(0, 1, 2))  // Line 3
  ];
  
  var goal := Or(Or(Atom("A"), Atom("B")), Atom("C"));  // Define a new local name to hold a value
  
  assert |proof| > 0;
  assert ValidProof(proof);
  assert Proves(proof, goal);
  
  // Disjunction elimination test (A ∨ (B ∨ C) ⊢ (A ∨ B) ∨ C) passed!
}


// --- method `TestImpliesIntro` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesIntro()
{
  // Prove: A → (A ∨ B)
  
  var proof: Proof := [  // Define a new local name to hold a value
    // Subproof: Assume A, derive A ∨ B
    Subproof(
      Atom("A"),  // assumption
      [
        Line(Atom("A"), Assumption),                              // 0: Assume A
        Line(Or(Atom("A"), Atom("B")), OrIntroLeft(0, Atom("B"))) // 1: A ∨ B
      ]
    ),  // Subproof at index 0
    
    // Discharge the subproof to get A → (A ∨ B)
    Line(
      Implies(Atom("A"), Or(Atom("A"), Atom("B"))),
      ImpliesIntro(0)  // Reference the subproof at index 0
    )
  ];
  
  var goal := Implies(Atom("A"), Or(Atom("A"), Atom("B")));  // Define a new local name to hold a value
  
  assert |proof| > 0;
  assert ValidProof(proof);  // The proof should be valid
  assert Proves(proof, goal);  // The proof should prove the goal

}


// --- method `TestImpliesIntroNested` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesIntroNested()
{
  // Prove: P → (Q → P)

  var proof: Proof := [  // Define a new local name to hold a value
    // Outer subproof: assume P, derive (Q → P)
    Subproof(
      Atom("P"),
      [
        Line(Atom("P"), Assumption),  // 0s: assume P

        // Inner subproof: assume Q, derive P
        Subproof(
          Atom("Q"),
          [
            Line(Atom("Q"), Assumption),  // 0ss: assume Q
            Line(Atom("P"), Assumption)   // 1ss: restate P (simple mode: duplicate assumption)
          ]
        ),  // Subproof at index 1s

        // Discharge inner subproof to get Q → P
        Line(Implies(Atom("Q"), Atom("P")), ImpliesIntro(1))
      ]
    ),  // Subproof at index 0

    // Discharge outer subproof to get P → (Q → P)
    Line(
      Implies(Atom("P"), Implies(Atom("Q"), Atom("P"))),
      ImpliesIntro(0)
    )
  ];

  var goal := Implies(Atom("P"), Implies(Atom("Q"), Atom("P")));  // Define a new local name to hold a value

  assert |proof| > 0;
  assert ValidProof(proof);
  assert Proves(proof, goal);

  print "Nested ImpliesIntro (P → (Q → P)) test passed!\n";
}



// Basic correctness tests for proof validation.

// --- method `test` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method test()
{
  // CONJUNCTION ELIMINATION/INTRODUCTION
  var x: Proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))
  ];
  assert |x| == 3;
  assert(CheckProof(x) == true);

  var y: Proof := [Line(Atom("p"), Assumption), Line(Atom("q"), Assumption), Line(Atom("p"), AndIntro(0, 1))];  // Define a new local name to hold a value
  assert |y| == 3;
  assert(ValidLine(y, 2) == false);
  assert(CheckProof(y) == false);

  var c: Proof := [Line(And(Atom("p"), Atom("q")), Assumption), Line(Atom("q"), AndElimRight(0))];  // Define a new local name to hold a value
  assert |c| == 2;
  assert(CheckProof(c) == true);

  var d: Proof := [Line(And(Atom("p"), Atom("q")), Assumption), Line(Atom("p"), AndElimLeft(0))];  // Define a new local name to hold a value
  assert |d| == 2;
  assert(CheckProof(d) == true);

  var e: Proof := [Line(And(Atom("p"), Atom("q")), Assumption), Line(Atom("q"), AndElimLeft(0))];  // Define a new local name to hold a value
  assert |e| == 2;
  assert(ValidLine(e, 1) == false);
  assert(CheckProof(e) == false);

  // IMPLICATION ELIMINATION
  var z: Proof := [Line(Atom("p"), Assumption), Line(Implies(Atom("p"), Atom("q")), Assumption), Line(Atom("q"), ImpliesElim(1, 0))];  // Define a new local name to hold a value
  assert |z| == 3;
  assert(CheckProof(z) == true);

  var a: Proof := [Line(Atom("p"), Assumption), Line(Implies(Atom("p"), Atom("q")), Assumption), Line(Atom("p"), ImpliesElim(1, 0))];  // Define a new local name to hold a value
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


// --- method `TestAssumptionSimple` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAssumptionSimple()
{
  var proof := [Line(Atom("p"), Assumption)];  // Define a new local name to hold a value
  assert ValidLine(proof, 0);
  assert CheckProof(proof);
}


// --- method `TestAssumptionComplex` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAssumptionComplex()
{
  var proof := [Line(And(Atom("p"), Atom("q")), Assumption)];  // Define a new local name to hold a value
  assert ValidLine(proof, 0);
  assert CheckProof(proof);
}


// --- method `TestMultipleAssumptions` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestMultipleAssumptions()
{
  var proof := [  // Define a new local name to hold a value
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


// --- method `TestAndIntroValid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroValid()
{
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}


// --- method `TestAndIntroReverseOrder` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroReverseOrder()
{
  // Can combine in any order
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("q"), Atom("p")), AndIntro(1, 0))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}


// --- method `TestAndIntroWrongFormula` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroWrongFormula()
{
  // Formula doesn't match the two lines being combined
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Atom("r"), AndIntro(0, 1))  // Should be And(p, q)
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}


// --- method `TestAndIntroWrongFormulaPartial` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroWrongFormulaPartial()
{
  // One side is correct, other is wrong
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("r")), AndIntro(0, 1))  // Right side should be q
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}


// --- method `TestAndIntroFutureReference` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroFutureReference()
{
  // Referencing a line that comes after
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), AndIntro(1, 2)),
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption)
  ];
  assert !ValidLine(proof, 0);
  assert !CheckProof(proof);
}


// --- method `TestAndIntroSelfReference` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroSelfReference()
{
  // Line cannot reference itself
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(And(Atom("p"), Atom("p")), AndIntro(1, 0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestAndIntroSameLineTwice` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroSameLineTwice()
{
  // Using same line for both sides is valid if formula matches
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(And(Atom("p"), Atom("p")), AndIntro(0, 0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestAndIntroNested` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndIntroNested()
{
  // Building nested And formulas
  var proof := [  // Define a new local name to hold a value
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


// --- method `TestAndElimLeftValid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimLeftValid()
{
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), AndElimLeft(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestAndElimLeftWrongFormula` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimLeftWrongFormula()
{
  // Extracting wrong side (should be left, got right)
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), AndElimLeft(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestAndElimLeftNotAnd` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimLeftNotAnd()
{
  // Trying to eliminate from non-And formula
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("p"), AndElimLeft(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestAndElimLeftFromOr` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimLeftFromOr()
{
  // Trying to eliminate from Or (wrong operator)
  var proof := [  // Define a new local name to hold a value
    Line(Or(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), AndElimLeft(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestAndElimLeftNested` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimLeftNested()
{
  // Eliminating from nested And
  var proof := [  // Define a new local name to hold a value
    Line(And(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(And(Atom("p"), Atom("q")), AndElimLeft(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestAndElimLeftFutureReference` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimLeftFutureReference()
{
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), AndElimLeft(1)),
    Line(And(Atom("p"), Atom("q")), Assumption)
  ];
  assert !ValidLine(proof, 0);
  assert !CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 4. AND ELIMINATION RIGHT TESTS
// ----------------------------------------------------------------------------


// --- method `TestAndElimRightValid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimRightValid()
{
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), AndElimRight(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestAndElimRightWrongFormula` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimRightWrongFormula()
{
  // Extracting wrong side (should be right, got left)
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), AndElimRight(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestAndElimRightNotAnd` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimRightNotAnd()
{
  var proof := [  // Define a new local name to hold a value
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), AndElimRight(0))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestAndElimRightNested` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAndElimRightNested()
{
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), And(Atom("q"), Atom("r"))), Assumption),
    Line(And(Atom("q"), Atom("r")), AndElimRight(0))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 5. IMPLIES ELIMINATION (MODUS PONENS) TESTS
// ----------------------------------------------------------------------------


// --- method `TestImpliesElimValid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimValid()
{
  var proof := [  // Define a new local name to hold a value
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}


// --- method `TestImpliesElimReverseOrder` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimReverseOrder()
{
  // Order of arguments matters: first is implication, second is antecedent
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), ImpliesElim(1, 0))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}


// --- method `TestImpliesElimWrongConsequent` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimWrongConsequent()
{
  // Result should be q, not p
  var proof := [  // Define a new local name to hold a value
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), Assumption),
    Line(Atom("p"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}


// --- method `TestImpliesElimWrongAntecedent` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimWrongAntecedent()
{
  // Second line doesn't match left side of implication
  var proof := [  // Define a new local name to hold a value
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("r"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}


// --- method `TestImpliesElimNotImplication` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimNotImplication()
{
  // First line is not an implication
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}


// --- method `TestImpliesElimFromAnd` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimFromAnd()
{
  // Trying to use And as if it were Implies
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("p"), Assumption),
    Line(Atom("q"), ImpliesElim(0, 1))
  ];
  assert !ValidLine(proof, 2);
  assert !CheckProof(proof);
}


// --- method `TestImpliesElimNested` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimNested()
{
  // Implication with complex formulas
  var proof := [  // Define a new local name to hold a value
    Line(Implies(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Atom("r"), ImpliesElim(0, 1))
  ];
  assert ValidLine(proof, 2);
  assert CheckProof(proof);
}


// --- method `TestImpliesElimChained` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimChained()
{
  // Using result of one modus ponens in another
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Implies(Atom("p"), Atom("q")), Assumption),
    Line(Atom("q"), ImpliesElim(1, 0)),
    Line(Implies(Atom("q"), Atom("r")), Assumption),
    Line(Atom("r"), ImpliesElim(3, 2))
  ];
  assert ValidLine(proof, 4);
  assert CheckProof(proof);
}


// --- method `TestImpliesElimFutureReference` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestImpliesElimFutureReference()
{
  var proof := [  // Define a new local name to hold a value
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


// --- method `TestOrIntroLeftValid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroLeftValid()
{
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), Atom("q")), OrIntroLeft(0, Atom("q")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestOrIntroLeftWrongLeft` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroLeftWrongLeft()
{
  // Left side of Or doesn't match referenced line
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Or(Atom("r"), Atom("q")), OrIntroLeft(0, Atom("q")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestOrIntroLeftWrongRight` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroLeftWrongRight()
{
  // Right side of Or doesn't match provided formula
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), Atom("r")), OrIntroLeft(0, Atom("q")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestOrIntroLeftNotOr` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroLeftNotOr()
{
  // Result is not an Or formula
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("p"), OrIntroLeft(0, Atom("q")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestOrIntroLeftComplex` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroLeftComplex()
{
  // Adding complex formula to right
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), And(Atom("q"), Atom("r"))), OrIntroLeft(0, And(Atom("q"), Atom("r"))))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestOrIntroLeftFromComplex` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroLeftFromComplex()
{
  // Starting with complex formula on left
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Or(And(Atom("p"), Atom("q")), Atom("r")), OrIntroLeft(0, Atom("r")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestOrIntroLeftFutureReference` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroLeftFutureReference()
{
  var proof := [  // Define a new local name to hold a value
    Line(Or(Atom("p"), Atom("q")), OrIntroLeft(1, Atom("q"))),
    Line(Atom("p"), Assumption)
  ];
  assert !ValidLine(proof, 0);
  assert !CheckProof(proof);
}

// ----------------------------------------------------------------------------
// 7. OR INTRODUCTION RIGHT TESTS
// ----------------------------------------------------------------------------


// --- method `TestOrIntroRightValid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroRightValid()
{
  var proof := [  // Define a new local name to hold a value
    Line(Atom("q"), Assumption),
    Line(Or(Atom("p"), Atom("q")), OrIntroRight(0, Atom("p")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestOrIntroRightWrongRight` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroRightWrongRight()
{
  // Right side of Or doesn't match referenced line
  var proof := [  // Define a new local name to hold a value
    Line(Atom("q"), Assumption),
    Line(Or(Atom("p"), Atom("r")), OrIntroRight(0, Atom("p")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestOrIntroRightWrongLeft` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroRightWrongLeft()
{
  // Left side of Or doesn't match provided formula
  var proof := [  // Define a new local name to hold a value
    Line(Atom("q"), Assumption),
    Line(Or(Atom("r"), Atom("q")), OrIntroRight(0, Atom("p")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestOrIntroRightNotOr` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroRightNotOr()
{
  var proof := [  // Define a new local name to hold a value
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), OrIntroRight(0, Atom("p")))
  ];
  assert !ValidLine(proof, 1);
  assert !CheckProof(proof);
}


// --- method `TestOrIntroRightComplex` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroRightComplex()
{
  var proof := [  // Define a new local name to hold a value
    Line(And(Atom("p"), Atom("q")), Assumption),
    Line(Or(Atom("r"), And(Atom("p"), Atom("q"))), OrIntroRight(0, Atom("r")))
  ];
  assert ValidLine(proof, 1);
  assert CheckProof(proof);
}


// --- method `TestOrIntroRightVsLeft` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrIntroRightVsLeft()
{
  // Make sure Left and Right are different
  var proof1 := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Or(Atom("p"), Atom("q")), OrIntroLeft(0, Atom("q")))
  ];
  var proof2 := [  // Define a new local name to hold a value
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


// --- method `TestComplexProofValid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestComplexProofValid()
{
  // (p ∧ q) → r, p, q ⊢ r
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(Implies(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Atom("r"), ImpliesElim(2, 3))
  ];
  assert CheckProof(proof);
  assert Proves(proof, Atom("r"));
}


// --- method `TestComplexProofInvalid` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestComplexProofInvalid()
{
  // Same as above but wrong conclusion
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Implies(And(Atom("p"), Atom("q")), Atom("r")), Assumption),
    Line(Atom("p"), ImpliesElim(3, 2))  // Should be r
  ];
  assert Proves(proof, Atom("r")) == false;
}


// --- method `TestBuildAndDestroy` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestBuildAndDestroy()
{
  // Build conjunction, then take it apart
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1)),
    Line(Atom("p"), AndElimLeft(2)),
    Line(Atom("q"), AndElimRight(2))
  ];
  assert CheckProof(proof);
}


// --- method `TestOrAndMix` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestOrAndMix()
{
  // Mixing Or and And operations
  var proof := [  // Define a new local name to hold a value
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


// --- method `TestSingleLineProof` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestSingleLineProof()
{
  var proof := [Line(Atom("p"), Assumption)];  // Define a new local name to hold a value
  assert CheckProof(proof);
  assert Proves(proof, Atom("p"));
}


// --- method `TestLongChain` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestLongChain()
{
  // Long chain of implications
  var proof := [  // Define a new local name to hold a value
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


// --- method `TestMaxIndexReference` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestMaxIndexReference()
{
  // Reference the line immediately before
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption),
    Line(And(Atom("p"), Atom("q")), AndIntro(0, 1))
  ];
  assert ValidLine(proof, 2);
}


// --- method `TestAllJustificationsInOneProof` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestAllJustificationsInOneProof()
{
  // Use every type of justification
  var proof := [  // Define a new local name to hold a value
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


// --- method `TestDeeplyNestedFormulas` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestDeeplyNestedFormulas()
{
  var proof := [  // Define a new local name to hold a value
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


// --- method `TestProvesWithWrongGoal` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestProvesWithWrongGoal()
{
  var proof := [  // Define a new local name to hold a value
    Line(Atom("p"), Assumption),
    Line(Atom("q"), Assumption)
  ];
  assert !Proves(proof, Atom("r"));  // Proves q, not r
}


// --- method `TestProvesRequiresNonEmpty` ----------------------------------------------
// What this does:
//  • High-level purpose of this piece of the parser.
//  • Inputs/outputs are explained by the spec right below (see the
//    translated comments after `requires`/`ensures`).
//  • Skim this to understand its role before diving into the body.
// -----------------------------------------------------------------
method TestProvesRequiresNonEmpty()
{
  // Proves requires |proof| > 0
  var emptyProof: Proof := [];  // Define a new local name to hold a value
  // Cannot call Proves(emptyProof, Atom("p")) - precondition violation
}
