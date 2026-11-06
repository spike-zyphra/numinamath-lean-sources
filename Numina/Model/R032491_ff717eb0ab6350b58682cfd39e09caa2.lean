import Mathlib

theorem algebra_188202 :
    {(x, y, z) : ℝ × ℝ × ℝ | x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ y + z ≠ 0 ∧ z + x ≠ 0 ∧ x + y ≠ 0 ∧
      1 / x + 1 / (y + z) = 1 / 2 ∧ 1 / y + 1 / (z + x) = 1 / 3 ∧ 1 / z + 1 / (x + y) = 1 / 4} =
    {(23 / 10, 23 / 6, 23 / 2)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Taking the system of equations and proving the variables have the required values.
    rintro ⟨hx, hy, hz, h1, h2, h3, h4, h5, h6⟩
    have eq1 : x * (y + z) = 2 * (x + y + z) := by
      have h11 : x ≠ 0 := hx
      have h12 : y + z ≠ 0 := by assumption
      field_simp [h11, h12] at h4 ⊢
      linarith
    have eq2 : y * (z + x) = 3 * (x + y + z) := by
      have h11 : y ≠ 0 := hy
      have h12 : z + x ≠ 0 := by assumption
      field_simp [h11, h12] at h5 ⊢
      linarith
    have eq3 : z * (x + y) = 4 * (x + y + z) := by
      have h11 : z ≠ 0 := hz
      have h12 : x + y ≠ 0 := by assumption
      field_simp [h11, h12] at h6 ⊢
      linarith
    have eq4 : 2 * (x * y + y * z + z * x) = 9 * (x + y + z) := by
      nlinarith [eq1, eq2, eq3]
    have hS : x + y + z ≠ 0 := by
      by_contra h
      rw [show y + z = -x by linarith [h]] at eq1
      have hx0 : x = 0 := by 
        nlinarith [eq1, h]
      contradiction
    have eq5 : z * (y - x) = x + y + z := by
      have h1' : y * (z + x) - x * (y + z) = (x + y + z) := by 
        nlinarith [eq1, eq2]
      nlinarith [h1']
    have eq6 : x * (z - y) = x + y + z := by
      have h1' : z * (x + y) - y * (z + x) = (x + y + z) := by
        nlinarith [eq2, eq3]
      nlinarith [h1']
    have eq7 : 2 * x * z = y * (x + z) := by
      nlinarith [eq5, eq6, sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show y ≠ 0 by exact hy), sq_pos_of_ne_zero (show z ≠ 0 by exact hz)]
    have eq8 : y = x + (x + y + z) / z := by
      have h1 : z ≠ 0 := hz
      have h2 : (z * (y - x) ) = x + y + z := eq5
      field_simp at *
      nlinarith [eq5, hz]
    have eq9 : x = 23 / 10 := by
      -- Substitute y in eq4 and hS
      rw [eq8] at eq4
      field_simp [hz] at eq4 ⊢
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num), sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show z ≠ 0 by exact hz), sq_nonneg (x * z), sq_nonneg (x - z), sq_nonneg (x + y + z), sq_pos_of_ne_zero hS, sq_nonneg (x^2), sq_nonneg (z^2), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hz]
    have eq10 : y = 23 / 6 := by 
      rw [eq9] at eq8 eq2
      field_simp [hz] at eq8 eq2 ⊢
      nlinarith [sq_nonneg (x * z), sq_nonneg (x - z), sq_nonneg (x + y + z), sq_nonneg (z - (23 : ℝ) / 2), sq_nonneg (x - (23 : ℝ) / 10), sq_nonneg (y - (23 : ℝ) / 6), sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show z ≠ 0 by exact hz), sq_pos_of_ne_zero hS, sq_nonneg (z^2)]
    have eq11 : z = 23 / 2 := by
      rw [eq9, eq10] at eq1 eq2 eq3
      nlinarith [sq_nonneg (x * z), sq_nonneg (x - z), sq_nonneg (x + y + z), sq_nonneg (z - (23 : ℝ) / 2), sq_nonneg (x - (23 : ℝ) / 10), sq_nonneg (y - (23 : ℝ) / 6), sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show z ≠ 0 by exact hz), sq_pos_of_ne_zero hS, sq_nonneg (x^2), sq_nonneg (y^2)]
    exact ⟨eq9, eq10, eq11⟩
  · -- Taking the variables with given values and proving they solve the system.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num