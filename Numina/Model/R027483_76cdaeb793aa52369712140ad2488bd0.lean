import Mathlib

theorem algebra_191406 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : (1 - a / 100) * (1 + b / 100) = 1) :
    b = 100 * a / (100 - a) := by

  have h1 : 100 - a ≠ 0 := by 
    by_contra h2 
    have h3 : a = 100 := by linarith 
    rw [h3] at h 
    norm_num at h 
    all_goals linarith

  have eq5 : (100 - a) * b = 100 * a := by 
    have eq7 : (1 - a / 100) * (1 + b / 100) = 1 := h
    field_simp at eq7 ⊢ 
    <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, show 0 < 100 - a by nlinarith]

  have h8 : 100 - a ≠ 0 := h1 
  have : b = 100 * a / (100 - a) := by
    have h9 : (100 - a) * b = 100 * a := eq5 
    have h8' : 100 - a ≠ 0 := h8 
    field_simp [h8'] at h9 ⊢ 
    <;> nlinarith 
  exact_mod_cast this