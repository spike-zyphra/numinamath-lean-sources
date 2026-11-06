import Mathlib

theorem algebra_95084 {w z : ℝ} (hw : w ≠ 0) (hz : z ≠ 0) (h : (1 / w + 1 / z) / (1 / w - 1 / z) = 2014) :
    (w + z) / (w - z) = -2014 := by
  have h_eq : (1 / w + 1 / z) / (1 / w - 1 / z) = (z + w) / (z - w) := by
    have h1 : w ≠ 0 := hw
    have h2 : z ≠ 0 := hz
    field_simp
    <;> ring
  rw [h_eq] at h
  have h2 : z - w ≠ 0 := by 
    by_contra h2
    have h3 : (z + w) / (z - w) = 0 := by 
      rw [show z - w = 0 by linarith]
      norm_num 
    have h4 : (z + w) / (z - w) = 2014 := h
    linarith
  have h5 : w - z ≠ 0 := by
    intro h6
    have h6 : w - z = 0 := h6 
    have h7 : z - w = 0 := by
      linarith  
    contradiction 
  have h7 : (z + w) / (z - w) = 2014 := h 
  have h8 : z + w = 2014 * (z - w) := by
    have h9 : z - w ≠ 0 := h2
    field_simp [h9] at h7 ⊢
    all_goals 
      nlinarith 
  have h10 : (w + z) / (w - z) = -2014 := by 
    have h9 : w - z ≠ 0 := h5 
    field_simp [h9] at *
    linarith
  linarith [h10]