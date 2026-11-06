import Mathlib

theorem number_theory_170823 : ¬∃ n : ℕ, ∀ k : ℕ, (Nat.floor (10 ^ k * Real.sqrt 2)) % 10 = n := by 
  rintro ⟨n, hn⟩
  have h0 := hn 0
  have h1 := hn 1
  have h4 : Nat.floor (10 ^ (0 : ℕ) * Real.sqrt 2) = 1 := by
    have h141 : (10 : ℝ) ^ (0 : ℕ) * Real.sqrt 2 = Real.sqrt 2 := by 
      norm_num
    rw [h141]
    have h71 : 1 < Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h72 : Real.sqrt 2 < 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h91 : Nat.floor (Real.sqrt 2) = 1 := by
      rw [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith [h71, h72]
      all_goals
        try nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact h91
  have h50 : (10 : ℝ) ^ (1 : ℕ) * Real.sqrt 2 = 10 * Real.sqrt 2 := by 
    norm_num
  have h5 : Nat.floor (10 ^ (1 : ℕ) * Real.sqrt 2) = 14 := by
    rw [h50]
    have h714 : 14 < 10 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h715 : 10 * Real.sqrt 2 < 15 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h11 : Nat.floor (10 * Real.sqrt 2) = 14 := by 
      rw [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith [h714, h715]
      all_goals
        try nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact h11
  have eq1 : (Nat.floor (10 ^ (0 : ℕ) * Real.sqrt 2)) % 10 = n := h0
  rw [h4] at eq1
  have eq2 : (Nat.floor (10 ^ (1 : ℕ) * Real.sqrt 2)) % 10 = n := h1
  rw [h5] at eq2
  omega