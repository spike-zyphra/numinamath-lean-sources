import Mathlib

theorem inequalities_51935 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    (1 + 1 / x) * (1 + 1 / y) ≥ 9 := by
  have h1 : y = 1 - x := by linarith
  have h2 : x * y ≤ (1 / 4) := by
    rw [h1]
    have h3 : x * (1 - x) ≤ 1 / 4 := by
      have h4 : (x - 1 / 2) ^ 2 ≥ 0 := sq_nonneg (x - 1 / 2)
      linarith
    linarith
  have h3 : (1 + 1 / x) * (1 + 1 / y) = 1 + 2 / (x * y) := by
    have h4 : (1 + 1 / x) * (1 + 1 / y) = 1 + (1 / x + 1 / y) + (1 / (x * y)) := by
      field_simp [show 0 < x * y by nlinarith]
      <;> ring
    have h5 : 1 / x + 1 / y = 1 / (x * y) := by
      field_simp [show 0 < x * y by nlinarith]
      <;> nlinarith
    rw [h4]
    rw [h5]
    field_simp [show 0 < x * y by nlinarith]
    <;> ring
  rw [h3]
  have h7 : (x * y) > 0 := by
    positivity
  have h9 : (2 / (x * y)) ≥ 8 := by
    have h10 : 0 < x * y := by positivity
    apply (le_div_iff₀ (by nlinarith)).mpr
    nlinarith [h2, h7]
  linarith