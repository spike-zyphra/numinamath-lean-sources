import Mathlib

theorem algebra_192023 (d : ℝ) (h : d = 3) (vj v : ℝ)
    (hj : vj = 2 * v) (ht : d / vj = d / v - 15 / 60) :
    v = 6 := by
  rw [h] at ht
  rw [hj] at ht
  have h1 : v ≠ 0 := by
    by_contra h1
    have h1' : v = 0 := by linarith
    rw [h1'] at ht
    norm_num [h1'] at ht
  have h2 : 2 * v ≠ 0 := by
    intro h2
    have : v = 0 := by
      linarith
    contradiction
  have eq3 : 90 = 180 - 15 * v := by
    have h4 : v ≠ 0 := h1
    have eq1' : (3 : ℝ) / (2 * v) = (3 : ℝ) / v - 15 / 60 := ht
    have h5 : (3 / (2 * v) : ℝ) = (3 / v - 15 / 60 : ℝ) := by
      simpa using ht
    have h6 : v ≠ 0 := h1
    have h7 : 2 * v ≠ 0 := h2
    have eq8 : (3 / (2 * v) : ℝ) * (60 * v) = (3 / v - 15 / 60 : ℝ) * (60 * v) := by
      rw [h5]
    have eq9 : (3 / (2 * v) : ℝ) * (60 * v) = 90 := by
      have h8 : v ≠ 0 := h1
      field_simp [h8]
      <;> nlinarith
    have eq10 : (3 / v - 15 / 60 : ℝ) * (60 * v) = 180 - 15 * v := by
      have h8 : v ≠ 0 := h1
      field_simp [h8]
      <;> nlinarith
    rw [eq9, eq10] at eq8
    linarith
  have h3 : 15 * v = 90 := by 
    linarith [eq3]
  have h4 : v = 6 := by
    linarith
  exact_mod_cast h4