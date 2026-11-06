import Mathlib

theorem number_theory_195966 (n : ℕ) (h₀ : Odd n) (h₁ : ∏ i ∈ Finset.range 5, (n + 2 * i) = 135135) :
    n + 2 * 4 = 15 := by
  norm_num [Finset.prod_range_succ] at h₁ 
  have h2 : n ≤ 20 := by
    by_contra h
    push_neg at h
    have h4 : n ≥ 21 := by
      omega
    have h5 : n * (n + 2) * (n + 4) * (n + 6) * (n + 8) ≥ 21 * 23 * 25 * 27 * 29 := by
      have h6 : n ≥ 21 := h4
      have h7 : n + 2 ≥ 23 := by
        omega
      have h8 : n + 4 ≥ 25 := by
        omega
      have h9 : n + 6 ≥ 27 := by
        omega
      have h10 : n + 8 ≥ 29 := by
        omega
      have h11 : n * (n + 2) * (n + 4) * (n + 6) * (n + 8) ≥ 21 * 23 * 25 * 27 * 29 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals
          omega
      linarith
    nlinarith
  interval_cases n <;> omega