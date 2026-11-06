import Mathlib

theorem algebra_10592 : IsGreatest {x + 1 / x | (x : ℝ) (_ : x ≠ 0) (_ : x ^ 2 + 1 / x ^ 2 = 7)} 3 := by
  constructor
  · -- Show that 3 is indeed in the set
    use (3 + Real.sqrt 5) / 2, by
      have h1 : Real.sqrt 5 > 0 := by
        positivity
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    constructor
    · -- Show $x \neq 0$
      have h1 : Real.sqrt 5 > 0 := by
        positivity
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    · -- Show $x + 1 / x = 3$
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · -- Show that 3 is the greatest element in the set
    intro y hy
    rcases hy with ⟨x, hx0, hx2, h_eq⟩
    have h1 : (x + 1 / x) ^ 2 = 9 := by
      have h2 : (x + 1 / x) ^ 2 = x ^ 2 + 1 / x ^ 2 + 2 := by
        field_simp [hx0]
        nlinarith
      rw [h2]
      nlinarith
    have h2 : (x + 1 / x) ≤ 3 := by
      nlinarith [sq_nonneg ((x + 1 / x) - 3), sq_nonneg ((x + 1 / x) + 3)]
    nlinarith