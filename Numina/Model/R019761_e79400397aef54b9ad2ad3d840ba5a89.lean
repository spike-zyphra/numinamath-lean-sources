import Mathlib

theorem inequalities_234842 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    x / (1 + y) + y / (1 + x) ≤ 1 := by
  have h1 : 0 ≤ x := hx.1
  have h2 : x ≤ 1 := hx.2
  have h3 : 0 ≤ y := hy.1
  have h4 : y ≤ 1 := hy.2
  have h5 : 0 ≤ (1 + y) * (1 + x) := by positivity

  have h6 : x / (1 + y) + y / (1 + x) - 1 ≤ 0 := by
    have h7 : x / (1 + y) + y / (1 + x) - 1 = (x * (1 + x) + y * (1 + y) - (1 + y) * (1 + x)) / ((1 + y) * (1 + x)) := by 
      field_simp [(show 0 < 1 + y by linarith), (show 0 < 1 + x by linarith)]
      <;> ring
    rw [h7]
    have h8 : x * (1 + x) + y * (1 + y) - (1 + y) * (1 + x) ≤ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1/2), sq_nonneg (y - 1/2), 
        mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3), 
        mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), 
        mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h4)]
    have h9 : (x * (1 + x) + y * (1 + y) - (1 + y) * (1 + x)) / ((1 + y) * (1 + x)) ≤ (0 : ℝ) := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      positivity
    linarith
  linarith