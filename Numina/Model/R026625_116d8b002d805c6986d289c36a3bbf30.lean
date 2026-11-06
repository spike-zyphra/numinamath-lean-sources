import Mathlib

theorem number_theory_247467 :
    ∃ n : ℕ, n = ∑ i ∈ Finset.Icc 100 999, (if (Nat.digits 10 i).length = 3 ∧ (Nat.digits 10 i).toFinset.card = 3 ∧ (Nat.digits 10 i).all (fun d => d ≠ 0) then i else 0) ∧
    n.primeFactors.card ≥ 3 := by
  set n := ∑ i ∈ Finset.Icc 100 999, (if (Nat.digits 10 i).length = 3 ∧ (Nat.digits 10 i).toFinset.card = 3 ∧ (Nat.digits 10 i).all (fun d => d ≠ 0) then i else 0) 
  use n 
  constructor 
  · 
    rfl 
  · 
    native_decide