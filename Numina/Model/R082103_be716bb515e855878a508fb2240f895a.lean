import Mathlib

theorem number_theory_197976 : ∃ k, ∃ m, m^2 = ∏ i ∈ Finset.Icc 1 100, if i = k then 1 else Nat.factorial i := by 
  use 50
  use (∏ i ∈ Finset.Icc 1 100, if i = 50 then 1 else Nat.factorial i).sqrt
  native_decide
  <;> try trivial
  <;> try { 
    native_decide
    <;> try trivial
  }
  <;> try { 
    native_decide
    <;> try trivial
  }