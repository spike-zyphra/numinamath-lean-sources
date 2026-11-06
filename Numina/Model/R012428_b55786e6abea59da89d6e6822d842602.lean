import Mathlib

theorem algebra_309365 (a : ℝ) :
    (∃ x y, x^2 + 4 * (y - a)^2 = 4 ∧ y = x^2 / 2) ↔
    -1 ≤ a ∧ a ≤ 17 / 8 := by
  constructor
  · -- Assume there exists (x, y) satisfying both equations.
    rintro ⟨x, y, h1, h2⟩
    have eq1 : x^2 + 4 * (y - a)^2 = 4 := h1
    rw [h2] at eq1
    have eq2 : x^2 + (x^2 - 2 * a) ^ 2 = 4 := by
      nlinarith
    have h4 : x^2 ≥ 0 := by nlinarith [sq_nonneg x]
    have h6 : a ≤ 17 / 8 := by
      nlinarith [sq_nonneg (x^2 - 2 * a + (4 * a - 1) / 2), sq_nonneg (x^2 - (4 * a - 1) / 2), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 4 * a)]
    have h7 : -1 ≤ a := by
      nlinarith [sq_nonneg (x^2 - 2 * a + (4 * a - 1) / 2), sq_nonneg (x^2 - (4 * a - 1) / 2), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 4 * a)]
    constructor <;> linarith
  · -- Assume -1 ≤ a ∧ a ≤ 17 / 8.
    rintro ⟨h1, h2⟩
    have h3 : 0 ≤ 17 - 8 * a := by nlinarith
    have h4 : ∃ t, t ≥ 0 ∧ t ^ 2 + (1 - 4 * a) * t + (4 * a ^ 2 - 4) = 0 := by
      use (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2
      constructor
      · -- Show t ≥ 0.
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show 0 ≤ (17 - 8 * a : ℝ) by linarith)]
      · -- Show quadratic = 0.
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show 0 ≤ (17 - 8 * a : ℝ) by linarith)]
    rcases h4 with ⟨t, ht1, ht2⟩
    have h5 : ∃ x, x^2 = t := by
      use Real.sqrt t
      all_goals
        nlinarith [Real.sqrt_nonneg t, Real.sq_sqrt (show 0 ≤ (t : ℝ) by linarith)]
    rcases h5 with ⟨x, hx⟩
    use x
    use x^2 / 2
    constructor
    · -- ellipse equation
      nlinarith [ht2, hx, sq_nonneg (x^2 - 2 * a), sq_nonneg (x ^ 2 - 4 * a), Real.sqrt_nonneg t]
    · -- parabola equation
      all_goals linarith [hx]