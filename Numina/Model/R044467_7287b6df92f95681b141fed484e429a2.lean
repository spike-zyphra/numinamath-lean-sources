import Mathlib

open Real

theorem inequalities_92996 : IsLeast {n : ℕ | 0 < n ∧ √n - √(n - 1) < 0.01} 2501 := by
  constructor
  · -- Show 2501 is in the set
    constructor
    · norm_num
    · -- Show that √2501 - √2500 < 0.01
      have h1 : √(2501 : ℝ) < 50.01 := by
        rw [Real.sqrt_lt] <;> norm_num
      have h2 : √(2500 : ℝ) = 50 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : √(2501 : ℝ) - √(2500 : ℝ) < (0.01 : ℝ) := by
        rw [h2] at *
        nlinarith [h1]
      norm_num at h3 ⊢
      all_goals linarith
  · -- Show that 2501 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_ineq⟩
    by_contra h
    push_neg at h
    have h4 : n ≤ 2500 := by
      omega
    have h8 : (n : ℝ) ≤ (2500 : ℝ) := by
      exact_mod_cast h4
    have h5 : n ≥ 1 := by
      omega
    have h8 : (n - 1 : ℝ) ≥ (0 : ℝ) := by
      have hn1 : n ≥ 1 := h5
      have hn2 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hn1
      nlinarith
    have h9 : √(n : ℝ) - √(n - 1 : ℝ) ≥ (0.01 : ℝ) := by
      have h10 : √(n : ℝ) = √(n - 1 + 1 : ℝ) := by
        ring_nf
      rw [h10]
      nlinarith [ sq_nonneg (√((n - 1 : ℝ) + 1) - (√(n - 1 : ℝ) + (0.01 : ℝ))), 
          Real.sqrt_nonneg ((n - 1 : ℝ) + 1), 
          Real.sqrt_nonneg (n - 1 : ℝ), 
          sq_nonneg (√((n - 1 : ℝ) + 1) - √(n - 1 : ℝ) - (0.01 : ℝ)), 
          Real.sq_sqrt (show 0 ≤ (n - 1 : ℝ) + 1 by nlinarith), 
          Real.sq_sqrt (show 0 ≤ (n - 1 : ℝ) by nlinarith), 
          show (n - 1 : ℝ) ≤ (2499 : ℝ) by 
            have h0 : n ≤ 2500 := by omega 
            have h0 : (n : ℝ) ≤ (2500 : ℝ) := by exact_mod_cast h0 
            nlinarith 
        ]
    linarith