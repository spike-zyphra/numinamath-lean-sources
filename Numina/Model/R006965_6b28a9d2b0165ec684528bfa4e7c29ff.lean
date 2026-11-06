import Mathlib

theorem algebra_303925 : {(w, x, y, z) : ℝ × ℝ × ℝ × ℝ | (w + 8 * x + 3 * y + 5 * z = 20) ∧ (4 * w + 7 * x + 2 * y + 3 * z = -20) ∧ (6 * w + 3 * x + 8 * y + 7 * z = 20) ∧ (7 * w + 2 * x + 7 * y + 3 * z = -20)} = {(-8, -12/5, 12/5, 8)} := by
  ext ⟨w, x, y, z⟩
  simp
  constructor
  · -- Forward: Solving the system of equations leads to the unique solution
    rintro ⟨h1, h2, h3, h4⟩
    have h5 : w = -8 := by 
      linarith [h1, h2, h3, h4]
    have h6 : x = -12/5 := by 
      rw [h5] at h1 h2 h3 h4
      linarith [h1, h2, h3, h4]
    have h7 : y = 12/5 := by 
      rw [h5, h6] at h1 h2 h3 h4
      linarith [h1, h2, h3, h4]
    have h8 : z = 8 := by 
      rw [h5, h6, h7] at h1 h2 h3 h4
      linarith [h1, h2, h3, h4]
    simp [h5, h6, h7, h8]
  · -- Backward: Checking that the claimed solution actually satisfies the system
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num