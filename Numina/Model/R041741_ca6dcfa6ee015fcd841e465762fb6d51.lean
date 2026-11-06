import Mathlib

theorem algebra_5235 : {x : ℝ | (x^2 + 7 * x + 6)^2 + 7 * (x^2 + 7 * x + 6) + 6 = x} = {-3 + √3, -3 - √3, -4 + √2, -4 - √2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume h: (x^2 + 7 * x + 6)^2 + 7 * (x^2 + 7 * x + 6) + 6 = x
    intro h
    have h1 : (x^2 + 7 * x + 6)^2 + 7 * (x^2 + 7 * x + 6) + 6 - x = 0 := by linarith
    have h2 : (x^2 + 6 * x + 6) * (x^2 + 8 * x + 14) = 0 := by
      nlinarith [h1, sq_nonneg (x^2 + 7 * x + 6 + x + 3), sq_nonneg (x + 3), sq_nonneg (x + 4)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case $x^2 + 6x + 6 = 0$
      have h5 : (x - (-3 + Real.sqrt 3)) * (x - (-3 - Real.sqrt 3)) = 0 := by
        nlinarith [h3, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Case $x = -3 + \sqrt{3}$
        left
        linarith
      · -- Case $x = -3 - \sqrt{3}$
        right
        left
        nlinarith
    · -- Case $x^2 + 8x + 14 = 0$
      have h6 : (x - (-4 + Real.sqrt 2)) * (x - (-4 - Real.sqrt 2)) = 0 := by
        nlinarith [h4, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case $x = -4 + \sqrt{2}$
        right
        right
        left
        nlinarith
      · -- Case $x = -4 - \sqrt{2}$
        right
        right
        right
        nlinarith
  · -- Show the four roots satisfy the equation
    rintro (h | h | h | h)
    · -- Case $x = -3 + \sqrt{3}$
      rw [h]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Case $x = -3 - \sqrt{3}$
      rw [h]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Case $x = -4 + \sqrt{2}$
      rw [h]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case $x = -4 - \sqrt{2}$
      rw [h]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]