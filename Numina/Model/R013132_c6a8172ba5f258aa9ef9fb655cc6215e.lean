import Mathlib

theorem algebra_278498 (d v1 v2 v3 : ℝ) (h : d > 0) (h1 : v1 > 0) (h2 : v2 > 0) (h3 : v3 > 0)
    (h4 : v3 = v1 + 15) (h5 : v2 = v1 + 10) (h6 : d / v2 = d / v1 - a) (h7 : d / v3 = d / v1 - b) :
    2 / 3 < b / a ∧ b / a < 3 / 2 := by
  have eq1 : a = d / v1 - d / v2 := by
    field_simp [h6]
    <;> nlinarith
  have eq2 : b = d / v1 - d / v3 := by
    field_simp [h7]
    <;> nlinarith

  rw [h5] at eq1
  rw [h4] at eq2

  have eq5 : a = (10 * d) / (v1 * (v1 + 10)) := by
    rw [eq1]
    field_simp [(show v1 ≠ 0 by linarith), (show v1 + 10 ≠ 0 by nlinarith)]
    <;> ring

  have eq6 : b = (15 * d) / (v1 * (v1 + 15)) := by
    rw [eq2]
    field_simp [(show v1 ≠ 0 by linarith), (show v1 + 15 ≠ 0 by nlinarith)]
    <;> ring

  have eq7 : b / a = (3 * (v1 + 10)) / (2 * (v1 + 15)) := by
    rw [eq6, eq5]
    field_simp [(show v1 ≠ 0 by linarith), (show v1 + 10 ≠ 0 by nlinarith), (show v1 + 15 ≠ 0 by nlinarith)]
    <;> ring_nf

  have h8 : b / a < 3 / 2 := by
    rw [eq7]
    have h9 : v1 > 0 := h1
    have h11 : v1 + 15 > 0 := by linarith
    have h12 : (3 * (v1 + 10)) / (2 * (v1 + 15)) < 3 / 2 := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h9]
    linarith

  have h9 : 2 / 3 < b / a := by
    rw [eq7]
    have h9 : v1 > 0 := h1
    have h11 : v1 + 15 > 0 := by nlinarith
    have h12 : (2 / 3 : ℝ) < (3 * (v1 + 10)) / (2 * (v1 + 15)) := by
      apply (lt_div_iff' (by positivity)).mpr
      nlinarith [h9]
    linarith
  constructor
  · linarith [h9]
  · linarith [h8]