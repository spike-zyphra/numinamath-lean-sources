import Mathlib

theorem algebra_110231 (n : ℕ) (h₀ : n ≠ 0) (h₁ : (n / 3 : ℝ) + (n / 13 : ℝ) = n - 1) :
    n / 5 = 10 := by
  have h₀ : (n : ℝ) > 0 := by
    have : (n : ℝ) ≥ 1 := by
      have hn0 : n ≥ 1 := by
        by_contra h
        push_neg at h
        have h₄ : n = 0 := by
          omega
        omega
      exact_mod_cast hn0
    linarith
  have h₂ := h₁
  field_simp at h₁
  have h₃ : n ≤ 3 := by
    by_contra h
    push_neg at h
    have h₄ : n ≥ 4 := by omega
    have : (n : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h₄
    have : (n : ℝ) < (4 : ℝ) := by
      nlinarith [sq_nonneg ((n : ℝ)), sq_nonneg ((n - (1 : ℝ) : ℝ)), sq_nonneg ((n : ℝ) - (29 / 15 : ℝ)), sq_nonneg ((n : ℝ) - (39 / 23 : ℝ)), sq_nonneg ((n - 1 : ℝ) : ℝ), sq_nonneg ((n - 2 : ℝ) : ℝ)]
    linarith -- This should generate a contradiction
  interval_cases n <;> norm_num at h₁ <;> norm_num
  <;> all_goals try trivial <;> tauto
  <;> all_goals norm_num