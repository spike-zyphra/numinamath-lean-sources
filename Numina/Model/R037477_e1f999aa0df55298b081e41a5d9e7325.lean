import Mathlib

theorem algebra_286680 : IsLeast {x | x > (2 + Real.sqrt 3)^2 ∧ ∃ n : ℕ, x = n} 14 := by
  constructor
  · -- Show that 14 is in the set.
    constructor
    · -- Show that (14 : ℝ) > (2 + Real.sqrt 3) ^ 2
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 2 / 1)]
    · -- Show that ∃ n : ℕ, (14 : ℝ) = n
      use 14
      all_goals norm_num
  · -- Show that 14 is the least element in the set
    intro x hx
    rcases hx with ⟨hx1, ⟨n, hn⟩⟩
    by_contra h
    push_neg at h
    have hn13 : n < 14 := by
      by_contra h3
      push_neg at h3
      have : n ≥ 14 := by omega
      have hn14 : (n : ℝ) ≥ (14 : ℝ) := by exact_mod_cast this
      linarith [hn, hn14, hx1]
    have h3 : n ≤ 13 := by
      omega
    have h4 : (n : ℝ) ≤ (13 : ℝ) := by
      have h5 : n ≤ 13 := h3
      exact_mod_cast h5
    have hx2 : (x : ℝ) ≤ (13 : ℝ) := by
      have h7 : (x : ℝ) = (n : ℝ) := by
        linarith [hn]
      linarith [h7, h4]
    have h4 : (2 + Real.sqrt 3) ^ 2 > (13 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 2 / 1)]
    linarith [h4, hx2, hx1]