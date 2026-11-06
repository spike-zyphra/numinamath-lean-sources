import Mathlib

theorem algebra_67774 (v_f v_s : ℝ) (h_v : v_f > 0 ∧ v_s > 0)
    (h_meeting : (v_f + v_s) / (v_f - v_s) = 5) :
    v_f / v_s = 3 / 2 := by 
  have h1 : v_f - v_s ≠ 0 := by
    by_contra h
    have h2 : v_f = v_s := by linarith
    rw [h2] at h_meeting
    norm_num at h_meeting
    all_goals linarith
  have h2 : v_f + v_s = 5 * (v_f - v_s) := by 
    have h3 : v_f - v_s ≠ 0 := h1
    field_simp [h3] at h_meeting
    linarith
  have h3 : 4 * v_f = 6 * v_s := by 
    linarith [h2]
  have h4 : v_f = (3 / 2) * v_s := by 
    linarith [h3]
  have h5 : v_s > 0 := h_v.right
  have h6 : v_f / v_s = 3 / 2 := by
    have h7 : v_s > 0 := h5
    field_simp [h7]
    linarith [h4]
  exact h6