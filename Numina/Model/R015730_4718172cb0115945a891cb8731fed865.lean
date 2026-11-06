import Mathlib

theorem number_theory_193007 (n : ℕ) (h : n ∈ Finset.Icc 1 66) :
    (∑ i ∈ Finset.Icc 1 66 \ {n}, i) % 7 = 0 ↔ n = 6 ∨ n = 13 ∨ n = 20 ∨ n = 27 ∨ n = 34 ∨ n = 41 ∨ n = 48 ∨ n = 55 ∨ n = 62 := by 
  rw [Finset.mem_Icc] at h 
  rcases h with ⟨hn1, hn2⟩
  interval_cases n <;> try { 
    native_decide 
  }
  <;> try { 
    omega 
  }