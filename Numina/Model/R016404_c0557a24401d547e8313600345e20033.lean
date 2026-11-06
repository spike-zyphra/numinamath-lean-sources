import Mathlib

theorem algebra_214705 {x y z : ℝ} (h1 : x * (y + z) = 3) (h2 : y * (x + z) = -32)
    (h3 : z * (x + y) = -5) :
    (x = -3 ∧ y = 4 ∧ z = -5) ∨ (x = 3 ∧ y = -4 ∧ z = 5) := by
  have eq1 : x * y + x * z = 3 := by
    linarith
  have eq2 : x * y + y * z = -32 := by
    linarith
  have eq3 : x * z + y * z = -5 := by
    linarith
  have eq4 : x * z - y * z = 35 := by
    linarith
  have eq5 : z * (x - y) = 35 := by
    linarith [eq4]
  have eq6 : z * (x + y) = -5 := by
    linarith [h3]
  have h4 : z ≠ 0 := by
    by_contra h
    rw [h] at eq5 eq6
    nlinarith
  have eq7 : x = 15 / z := by
    have eq8 : x - y = 35 / z := by
      have h5 : z * (x - y) = 35 := eq5
      field_simp [h4] at h5 ⊢
      <;> linarith
    have eq9 : x + y = -5 / z := by
      have h6 : z * (x + y) = -5 := eq6
      field_simp [h4] at h6 ⊢
      <;> linarith 
    have eq10 : x = 15 / z := by
      field_simp [h4] at eq8 eq9 ⊢
      nlinarith
    assumption
  have eq8 : y = -20 / z := by
    have eq8 : x - y = 35 / z := by
      have h5 : z * (x - y) = 35 := eq5
      field_simp [h4] at h5 ⊢
      <;> linarith
    have eq9 : x + y = -5 / z := by
      have h6 : z * (x + y) = -5 := eq6
      field_simp [h4] at h6 ⊢
      <;> linarith 
    have eq10 : y = -20 / z := by
      field_simp [h4] at eq8 eq9 ⊢
      nlinarith
    assumption
  have eq9 : z ^ 2 = 25 := by
    have eq11 : x * y + y * z = -32 := eq2
    rw [show x = 15 / z by linarith [eq7]] at eq11
    rw [show y = -20 / z by linarith [eq8]] at eq11
    field_simp [h4] at eq11 ⊢
    <;> nlinarith
  have eq10 : z = 5 ∨ z = -5 := by
    have h1 : z ^ 2 - 25 = 0 := by nlinarith
    have h2 : (z - 5) * (z + 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · left
      linarith
    · right
      linarith
  cases eq10 with
  | inl hz5 =>
    -- z = 5
    have h5 : x = 3 := by
      rw [show z = 5 by linarith [hz5]] at eq7
      norm_num at eq7 ⊢
      <;> linarith
    have h6 : y = -4 := by
      rw [show z = 5 by linarith [hz5]] at eq8
      norm_num at eq8 ⊢
      <;> linarith
    right
    constructor
    · linarith [h5]
    constructor
    · linarith [h6]
    · linarith [hz5]
  | inr hz5 =>
    -- z = -5
    have h5 : x = -3 := by
      rw [show z = -5 by linarith [hz5]] at eq7
      norm_num at eq7 ⊢
      <;> linarith
    have h6 : y = 4 := by
      rw [show z = -5 by linarith [hz5]] at eq8
      norm_num at eq8 ⊢
      <;> linarith
    left
    constructor
    · linarith [h5]
    constructor
    · linarith [h6]
    · linarith [hz5]