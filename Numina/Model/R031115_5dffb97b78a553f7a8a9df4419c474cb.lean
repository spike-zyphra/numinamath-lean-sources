import Mathlib

theorem number_theory_181963 (n : ℕ) (h₀ : Even n) (h₁ : ∑ i ∈ Finset.range 10, (n + 2 * i) = 5370) :
    (Nat.primeFactors (n + 2 * 9)) = {2, 3, 7, 13} := by 
  norm_num [Finset.sum_range_succ] at h₁ 
  have h2 : n = 528 := by 
    omega 
  rw [h2] 
  native_decide