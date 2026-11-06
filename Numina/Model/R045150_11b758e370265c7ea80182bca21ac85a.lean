import Mathlib

theorem algebra_187068 {x y : ℝ} (h1 : x + y + x / y = 9) (h2 : (x + y) * x / y = 20) :
    (x = 10 / 3 ∧ y = 2 / 3) ∨ (x = 4 ∧ y = 1) := by
  have hy : y ≠ 0 := by
    by_contra h
    rw [h] at h1 h2
    norm_num at h1 h2
  have eq1 : x * y + y ^ 2 + x = 9 * y := by
    have h1' : x + y + x / y = 9 := h1
    have h3 : y ≠ 0 := hy
    field_simp at h1'
    linarith
  have eq2 : x ^ 2 + x * y = 20 * y := by
    have h2' : (x + y) * x / y = 20 := h2
    have h3 : y ≠ 0 := hy
    field_simp at h2'
    linarith
  have eq3 : x ^ 2 - 9 * (x * y) + 20 * y ^ 2 = 0 := by
    nlinarith [eq1, eq2]
  have ht : (x / y) ^ 2 - 9 * (x / y) + 20 = 0 := by
    have h4 : y ≠ 0 := hy
    have eq3' : x ^ 2 - 9 * (x * y) + 20 * y ^ 2 = 0 := eq3
    have eq4 : (x / y) ^ 2 - 9 * (x / y) + 20 = (x ^ 2 - 9 * (x * y) + 20 * y ^ 2) / (y ^ 2) := by
      field_simp [h4]
      ring
    rw [eq4]
    rw [eq3']
    norm_num
  have h4 : (x / y - 4) * (x / y - 5) = 0 := by
    nlinarith [ht]
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- case t = 4
    have ht4 : x / y = 4 := by linarith
    have h7 : x = 4 * y := by
      have ht4' : x / y = 4 := ht4
      have h4 : y ≠ 0 := hy
      field_simp at ht4'
      linarith
    rw [show x = 4 * y by linarith [h7]] at eq2
    have hy1 : y = 1 := by
      have : 20 * y ^ 2 - 20 * y = 0 := by
        nlinarith
      have : y * (20 * y - 20) = 0 := by
        linarith
      cases' (mul_eq_zero.1 this) with h4 h5
      · 
        exfalso
        tauto
      · 
        nlinarith
    have hx1 : x = 4 := by
      nlinarith [h7, hy1]
    right
    simp [hx1, hy1]
  · -- case t = 5
    have ht5 : x / y = 5 := by linarith
    have h7 : x = 5 * y := by
      have ht5' : x / y = 5 := ht5
      have h4 : y ≠ 0 := hy
      field_simp at ht5'
      linarith
    rw [show x = 5 * y by linarith [h7]] at eq2
    have hy2 : y = 2 / 3 := by
      nlinarith [sq_pos_of_ne_zero (show y ≠ 0 by exact hy)]
    have hx2 : x = 10 / 3 := by
      nlinarith [h7, hy2]
    left
    simp [hx2, hy2]