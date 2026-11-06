import Mathlib

theorem algebra_177325 {x : ℝ} (hx : x > 0) (h : (13 / x) * (x - 0.5) ≥ 55 ∧ (13 / x) * x ≤ 64) :
    x = 2.5 := by
  have h1 : (13 / x) * (x - 0.5) ≥ 55 := h.1
  have h2 : (13 / x) * x ≤ 64 := h.2

  have eq1 : (13 / x) * (x - 0.5) = 13 * (1 - (0.5 / x)) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring

  have eq2 : (13 / x) * x = 13 := by
    field_simp

  rw [eq1] at h1
  rw [eq2] at h2
  norm_num at h1 h2
  
  -- This will derive contradiction since impossible to have.

  all_goals
    try { 
      have h3 : (0.5 / x) > 0 := by
        apply div_pos
        norm_num
        all_goals linarith

      nlinarith
    }
    all_goals nlinarith