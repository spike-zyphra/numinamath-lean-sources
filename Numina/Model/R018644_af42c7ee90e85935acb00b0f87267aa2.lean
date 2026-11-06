import Mathlib

theorem algebra_313985 (x : ℝ) :
    ¬(5 < (x ^ 2 + 34 * x - 71) / (x ^ 2 + 2 * x - 7) ∧ (x ^ 2 + 34 * x - 71) / (x ^ 2 + 2 * x - 7) < 9) := by
  intro h
  rcases h with ⟨h1, h2⟩
  have h3 : x ^ 2 + 2 * x - 7 ≠ 0 := by
    by_contra h'
    have h4 : (x ^ 2 + 34 * x - 71) / (x ^ 2 + 2 * x - 7) = 0 := by
      rw [show x ^ 2 + 2 * x - 7 = (0 : ℝ) by nlinarith]
      norm_num
      <;> nlinarith
    linarith
  by_cases h6 : 0 < x ^ 2 + 2 * x - 7
  · -- Case where the denominator is positive.
    have h7 : 5 * (x ^ 2 + 2 * x - 7) < x ^ 2 + 34 * x - 71 := by
      have h8 : (x ^ 2 + 34 * x - 71) / (x ^ 2 + 2 * x - 7) > 5 := by linarith
      apply (lt_div_iff₀ (by linarith)).mp at h8
      nlinarith
    have h8 : 4 * x ^ 2 - 24 * x + 36 < (0 : ℝ) := by nlinarith
    have h9 : (x - 3) ^ 2 < (0 : ℝ) := by
      nlinarith
    have h10 : (x - 3) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith
  · -- Case where the denominator ≤ 0.
    have h7 : x ^ 2 + 2 * x - 7 ≤ 0 := by nlinarith
    by_cases h8 : x ^ 2 + 2 * x - 7 < (0 : ℝ)
    · -- Case where the denominator < 0.
      -- Prove contradiction with h2.
      have h11 : (x ^ 2 + 34 * x - 71) / (x ^ 2 + 2 * x - 7) < 9 := by linarith
      have h12 : x ^ 2 + 34 * x - 71 > 9 * (x ^ 2 + 2 * x - 7) := by
        have h13 : (x ^ 2 + 34 * x - 71) / (x ^ 2 + 2 * x - 7) < 9 := h11
        apply (div_lt_iff_of_neg' (by nlinarith)).mp at h13
        nlinarith
        all_goals nlinarith
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 3)]
    · -- Case where the denominator = 0.
      have h9 : x ^ 2 + 2 * x - 7 = 0 := by nlinarith
      contradiction