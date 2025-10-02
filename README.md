# Katanamu (కతనం)

**Katanamu** (కతనం, meaning *Reason* or *Cause* in Mēlimi Telugu) is a minimal 
**natural-deduction proof checker** written in **Dafny** for propositional logic.  

It represents logical formulas (`Atom`, `And`, `Or`, `Not`, `Implies`, `Iff`) 
and validates proofs line by line using explicit justifications 
(`Assumption`, `AndIntro`, `AndElim`, `ImpliesElim`, `OrIntro`).  

`Katanamu` ensures **no forward references** and provides predicates to check 
validity (`ValidProof`), functionally assert correctness (`CheckProof`), and 
verify that a proof derives its intended conclusion (`Proves`).

---
