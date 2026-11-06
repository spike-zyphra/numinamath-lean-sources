import Mathlib

theorem algebra_14608 : IsGreatest { |x| + |y| | (x : ℝ) (y : ℝ) (h : x^2 + y^2 = 1) } √2 := by
  constructor
  · -- First part: Show that √2 is in the set.
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2
    constructor
    · -- Show that |Real.sqrt 2 / 2| + |Real.sqrt 2 / 2| = √2.
      have h1 : Real.sqrt 2 > 0 := by
        positivity
      have h2 : Real.sqrt 2 / 2 ≥ 0 := by
        linarith [h1]
      have h3 : |((Real.sqrt 2 / 2) : ℝ)| = Real.sqrt 2 / 2 := by
        rw [abs_of_nonneg h2]
      have h4 : |((Real.sqrt 2 / 2) : ℝ)| = Real.sqrt 2 / 2 := by
        rw [abs_of_nonneg h2]
      linarith [h3, h4, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show that (Real.sqrt 2 / 2)^2 + (Real.sqrt 2 / 2)^2 = 1.
      have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 + (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 := by
        have h5 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        nlinarith [h5, Real.sqrt_nonneg 2]
      linarith [h1]
  · -- Second part: Show that √2 is the greatest element in the set.
    intro k hk
    rcases hk with ⟨x, y, h, hk⟩
    have h1 : ( |x| + |y| ) ^ 2 ≤ 2 * (x^2 + y^2) := by
      cases' abs_cases x with hx hx
      · -- |x| = x
        cases' abs_cases y with hy hy
        · -- |y| = y
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2)]
        · -- |y| = -y
          nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 - y^2)]
      · -- |x| = -x
        cases' abs_cases y with hy hy
        · -- |y| = y
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2)]
        · -- |y| = -y
          nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 - y^2)]
    have h2 : ( |x| + |y| ) ^ 2 ≤ 2 := by
      have h3 : x^2 + y^2 = 1 := h
      nlinarith [h1, h3]
    have h3 : |x| + |y| ≤ Real.sqrt 2 := by
      have h4 : ( |x| + |y| ) ^ 2 ≤ (2 : ℝ) := by
        nlinarith [h2]
      have h5 : ( |x| + |y| ) ≤ Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h4, Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      exact h5
    linarith [h3, Real.sqrt_nonneg (2 : ℝ), hk]