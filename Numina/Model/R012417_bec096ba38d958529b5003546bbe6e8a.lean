import Mathlib

theorem algebra_316295 (A B : Set ℝ) (hA : A = {x | x^2 - 5 * x + 6 < 0}) (hB : B = {x | x^2 - a * x + 5 = 0})
    (ha : ∃ x, x ∈ A ∧ x ∈ B) :
    2 * Real.sqrt 5 ≤ a ∧ a < 14 / 3 := by
  rcases ha with ⟨x, hx1, hx2⟩
  rw [hA] at hx1
  rw [hB] at hx2
  have h1 : x^2 - 5 * x + 6 < 0 := hx1
  have h2 : x^2 - a * x + 5 = 0 := hx2
  have h3 : 2 < x := by
    nlinarith
  have h4 : x < 3 := by
    nlinarith
  -- From $x^2 - a * x + 5 = 0$, solve for $a$:
  -- Rearranged: $a * x = x^2 + 5$
  -- Then $a = \frac{x^2 + 5}{x} = x + \frac{5}{x}$
  have h5 : a = x + 5 / x := by
    have hx_ne_zero : x ≠ 0 := by
      linarith
    field_simp
    nlinarith
  constructor
  · -- Prove the lower bound: $2 * Real.sqrt 5 ≤ a$
    rw [h5]
    have h7 : 0 < x := by nlinarith
    have h8 : x + 5 / x - 2 * Real.sqrt 5 ≥ 0 := by
      have h9 : x + 5 / x - 2 * Real.sqrt 5 = (x ^ 2 + 5 - 2 * Real.sqrt 5 * x) / x := by
        field_simp
        ring
      rw [h9]
      have h10 : x ^ 2 + 5 - 2 * Real.sqrt 5 * x ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (x - Real.sqrt 5)]
      apply div_nonneg
      linarith
      all_goals positivity
    have h9 : x + 5 / x ≥ 2 * Real.sqrt 5 := by
      linarith
    linarith
  · -- Prove the upper bound: $a < 14 / 3$
    rw [h5]
    have hx_pos : 0 < x := by linarith
    have hx3 : 3 * x ^ 2 - 14 * x + 15 < 0 := by
      nlinarith
    have : x + 5 / x < (14 / 3 : ℝ) := by
      have hx_pos : 0 < x := by linarith
      have : x + 5 / x - 14 / 3 < 0 := by
        have : x + 5 / x - 14 / 3 = (3 * x ^ 2 + 15 - 14 * x) / (3 * x) := by
          field_simp
          ring
        rw [this]
        apply div_neg_of_neg_of_pos
        · nlinarith
        all_goals nlinarith
      linarith
    nlinarith