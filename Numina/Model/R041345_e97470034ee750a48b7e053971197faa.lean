import Mathlib
open Real

theorem algebra_20001 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x^2 + y^2 = 1)
  (h : arccos ((4 * x + 3 * y) / 5) = arctan (y / x)) : tan (arctan (y / x)) = 1 / 3 := by

  have h1 : cos (arccos ((4 * x + 3 * y) / 5)) = (4 * x + 3 * y) / 5 := by
    apply Real.cos_arccos
    · -- Show -1 ≤ (4 * x + 3 * y) / 5
      have h2 : -1 ≤ (4 * x + 3 * y) / 5 := by
        nlinarith [sq_nonneg (x * 3 - y * 4), sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (x^2 + y^2 - 1)]
      linarith
    · -- Show (4 * x + 3 * y) / 5 ≤ 1
      have h3 : (4 * x + 3 * y) / 5 ≤ 1 := by
        nlinarith [sq_nonneg (x * 3 - y * 4), sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (x^2 + y^2 - 1)]
      linarith

  have h2 : cos (arctan (y / x)) = x / Real.sqrt (x^2 + y^2) := by
    rw [Real.cos_arctan]
    field_simp
    <;> nlinarith

  have h3 : Real.sqrt (x^2 + y^2) = 1 := by
    have h4 : x^2 + y^2 = (1 : ℝ) := by
      linarith [hxy]
    rw [h4]
    rw [Real.sqrt_one]

  have h4 : cos (arctan (y / x)) = x := by
    rw [h2, h3]
    all_goals field_simp
    <;> nlinarith

  -- From h: arccos((4 * x + 3 * y) / 5) = arctan (y / x)
  -- Taking cos of both sides
  have h5 : (4 * x + 3 * y) / 5 = x := by
    have h6 : cos (arccos ((4 * x + 3 * y) / 5)) = cos (arctan (y / x)) := by
      rw [h]
    rw [h1, h4] at h6
    linarith

  have h6 : x = 3 * y := by
    nlinarith [h5]

  have h7 : y / x = 1 / 3 := by
    have h8 : x ≠ 0 := by linarith
    have h9 : y = x / 3 := by
      nlinarith [h6]
    field_simp [h8]
    nlinarith [h9]

  have h8 : tan (arctan (y / x)) = y / x := by
    rw [tan_arctan]

  rw [h8]
  linarith [h7]