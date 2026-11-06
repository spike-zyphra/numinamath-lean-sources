import Mathlib

theorem algebra_5740 (A : ℝ) (h : Real.sin A + Real.cos A ≠ 0 ∧ Real.sin A - Real.cos A ≠ 0 ∧
    (Real.sin A + Real.cos A) / (Real.sin A - Real.cos A) = 3) :
    (Real.sin A) ^ 4 - (Real.cos A) ^ 4 = 3 / 5 := by 
  have h1 : Real.sin A + Real.cos A ≠ 0 := h.1
  have h2 : Real.sin A - Real.cos A ≠ 0 := h.2.1
  have heq : (Real.sin A + Real.cos A) / (Real.sin A - Real.cos A) = 3 := h.2.2
  have eq1 : Real.sin A + Real.cos A = 3 * (Real.sin A - Real.cos A) := by
    field_simp [h2] at heq
    linarith [heq]
  have eq2 : Real.sin A = 2 * Real.cos A := by
    linarith [eq1]
  have h3 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
  have h4 : Real.sin A ^ 2 = 4 * Real.cos A ^ 2 := by 
    rw [show Real.sin A = 2 * Real.cos A by linarith [eq2]] 
    nlinarith 
  have h5 : Real.cos A ^ 2 = 1 / 5 := by 
    have eq3 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
    rw [show Real.sin A ^ 2 = 4 * Real.cos A ^ 2 by linarith [h4]] at eq3
    nlinarith 
  have h6 : Real.sin A ^ 2 = 4 / 5 := by 
    nlinarith [show Real.cos A ^ 2 = 1 / 5 by linarith [h5]]
  have h7 : Real.sin A ^ 4 - (Real.cos A) ^ 4 = (Real.sin A ^ 2 - Real.cos A ^ 2) * (Real.sin A ^ 2 + Real.cos A ^ 2) := by
    ring
  rw [h7]
  have h8 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
  have h9 : Real.sin A ^ 2 - Real.cos A ^ 2 = 3 / 5 := by
    nlinarith [show Real.sin A ^ 2 = 4 / 5 by linarith [h6], show Real.cos A ^ 2 = 1 / 5 by linarith [h5]]
  rw [h8, h9]
  all_goals linarith