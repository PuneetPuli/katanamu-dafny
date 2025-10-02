// Basic Example Proofs
// This file demonstrates common logical proofs using the proof checker

include "../src/ProofSystem.dfy"

// ============================================================================
// EXAMPLE 1: Modus Ponens
// ============================================================================
// If we have "P implies Q" and we have "P", then we can conclude "Q"

method ExampleModusPonens()
{
  var proof := [
    Line(Atom("P"), Assumption),
    Line(Implies(Atom("P"), Atom("Q")), Assumption),
    Line(Atom("Q"), ImpliesElim(1, 0))
  ];
  
  assert CheckProof(proof);
  assert Proves(proof, Atom("Q"));
  
  print "✓ Modus Ponens: From 'P → Q' and 'P', we derive 'Q'\n";
}

// ============================================================================
// EXAMPLE 2: Conjunction Introduction and Elimination
// ============================================================================
// Build a conjunction from two parts, then extract each part back

method ExampleConjunction()
{
  var proof := [
    Line(Atom("P"), Assumption),
    Line(Atom("Q"), Assumption),
    Line(And(Atom("P"), Atom("Q")), AndIntro(0, 1)),
    Line(Atom("P"), AndElimLeft(2)),
    Line(Atom("Q"), AndElimRight(2))
  ];
  
  assert CheckProof(proof);
  
  print "✓ Conjunction: Build 'P ∧ Q' from P and Q, then extract them back\n";
}

// ============================================================================
// EXAMPLE 3: Disjunction Introduction
// ============================================================================
// From P, we can prove "P or Q" (for any Q)

method ExampleDisjunction()
{
  var proof := [
    Line(Atom("P"), Assumption),
    Line(Or(Atom("P"), Atom("Q")), OrIntroLeft(0, Atom("Q"))),
    Line(Or(Atom("R"), Atom("P")), OrIntroRight(0, Atom("R")))
  ];
  
  assert CheckProof(proof);
  
  print "✓ Disjunction: From P, derive 'P ∨ Q' and 'R ∨ P'\n";
}

// ============================================================================
// EXAMPLE 4: Hypothetical Syllogism
// ============================================================================
// If P→Q and Q→R, then P→R (transitivity of implication)

method ExampleHypotheticalSyllogism()
{
  // Note: We prove this for specific P, Q, R given as assumptions
  // Not proving the general rule itself
  var proof := [
    Line(Atom("P"), Assumption),
    Line(Implies(Atom("P"), Atom("Q")), Assumption),
    Line(Atom("Q"), ImpliesElim(1, 0)),
    Line(Implies(Atom("Q"), Atom("R")), Assumption),
    Line(Atom("R"), ImpliesElim(3, 2))
  ];
  
  assert CheckProof(proof);
  assert Proves(proof, Atom("R"));
  
  print "✓ Hypothetical Syllogism: From P, P→Q, and Q→R, derive R\n";
}

// ============================================================================
// EXAMPLE 5: Complex Formula
// ============================================================================
// Working with nested formulas: ((P ∧ Q) → R)

method ExampleComplexFormula()
{
  var proof := [
    Line(Atom("P"), Assumption),
    Line(Atom("Q"), Assumption),
    Line(And(Atom("P"), Atom("Q")), AndIntro(0, 1)),
    Line(Implies(And(Atom("P"), Atom("Q")), Atom("R")), Assumption),
    Line(Atom("R"), ImpliesElim(3, 2))
  ];
  
  assert CheckProof(proof);
  assert Proves(proof, Atom("R"));
  
  print "✓ Complex Formula: From P, Q, and (P∧Q)→R, derive R\n";
}

// ============================================================================
// EXAMPLE 6: Simplification
// ============================================================================
// From P∧Q, we can derive just P (or just Q)

method ExampleSimplification()
{
  var proofForP := [
    Line(And(Atom("P"), Atom("Q")), Assumption),
    Line(Atom("P"), AndElimLeft(0))
  ];
  
  var proofForQ := [
    Line(And(Atom("P"), Atom("Q")), Assumption),
    Line(Atom("Q"), AndElimRight(0))
  ];
  
  assert CheckProof(proofForP);
  assert CheckProof(proofForQ);
  assert Proves(proofForP, Atom("P"));
  assert Proves(proofForQ, Atom("Q"));
  
  print "✓ Simplification: From P∧Q, derive P (or Q)\n";
}

// ============================================================================
// EXAMPLE 7: Addition
// ============================================================================
// From P, we can derive P∨Q (adding any disjunct)

method ExampleAddition()
{
  var proof := [
    Line(Atom("P"), Assumption),
    Line(Or(Atom("P"), Atom("Q")), OrIntroLeft(0, Atom("Q")))
  ];
  
  assert CheckProof(proof);
  assert Proves(proof, Or(Atom("P"), Atom("Q")));
  
  print "✓ Addition: From P, derive P∨Q\n";
}

// ============================================================================
// EXAMPLE 8: Building Complex Disjunctions
// ============================================================================

method ExampleComplexDisjunction()
{
  var proof := [
    Line(Atom("P"), Assumption),
    Line(Atom("Q"), Assumption),
    Line(And(Atom("P"), Atom("Q")), AndIntro(0, 1)),
    Line(Or(And(Atom("P"), Atom("Q")), Atom("R")), 
         OrIntroLeft(2, Atom("R")))
  ];
  
  assert CheckProof(proof);
  assert Proves(proof, Or(And(Atom("P"), Atom("Q")), Atom("R")));
  
  print "✓ Complex Disjunction: From P and Q, derive (P∧Q)∨R\n";
}

// ============================================================================
// EXAMPLE 9: Longer Proof Chain
// ============================================================================

method ExampleLongChain()
{
  var proof := [
    Line(Atom("A"), Assumption),
    Line(Implies(Atom("A"), Atom("B")), Assumption),
    Line(Atom("B"), ImpliesElim(1, 0)),
    Line(Implies(Atom("B"), Atom("C")), Assumption),
    Line(Atom("C"), ImpliesElim(3, 2)),
    Line(Implies(Atom("C"), Atom("D")), Assumption),
    Line(Atom("D"), ImpliesElim(5, 4)),
    Line(Implies(Atom("D"), Atom("E")), Assumption),
    Line(Atom("E"), ImpliesElim(7, 6))
  ];
  
  assert CheckProof(proof);
  assert Proves(proof, Atom("E"));
  
  print "✓ Long Chain: From A and multiple implications, derive E\n";
}

// ============================================================================
// EXAMPLE 10: Combining Multiple Rules
// ============================================================================

method ExampleCombination()
{
  var proof := [
    // Assumptions
    Line(Atom("P"), Assumption),
    Line(Atom("Q"), Assumption),
    
    // Build conjunction
    Line(And(Atom("P"), Atom("Q")), AndIntro(0, 1)),
    
    // Build disjunction
    Line(Or(And(Atom("P"), Atom("Q")), Atom("R")), 
         OrIntroLeft(2, Atom("R"))),
    
    // Another assumption
    Line(Implies(Or(And(Atom("P"), Atom("Q")), Atom("R")), Atom("S")), 
         Assumption),
    
    // Apply modus ponens
    Line(Atom("S"), ImpliesElim(4, 3))
  ];
  
  assert CheckProof(proof);
  assert Proves(proof, Atom("S"));
  
  print "✓ Combination: Using multiple rules together\n";
}

// ============================================================================
// RUN ALL EXAMPLES
// ============================================================================

method Main()
{
  print "Running example proofs...\n\n";
  
  ExampleModusPonens();
  ExampleConjunction();
  ExampleDisjunction();
  ExampleHypotheticalSyllogism();
  ExampleComplexFormula();
  ExampleSimplification();
  ExampleAddition();
  ExampleComplexDisjunction();
  ExampleLongChain();
  ExampleCombination();
  
  print "\n✓ All examples verified successfully!\n";
}