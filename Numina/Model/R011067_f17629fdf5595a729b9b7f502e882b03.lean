import Mathlib

theorem algebra_214829 (v_s v_t v_v d : ℝ) (h_v : v_s > 0 ∧ v_t > 0 ∧ v_v > 0) (hd : d > 0)
    (h_s_t_meet : v_s * (4 / 60) + v_t * (4 / 60) = d) (h_v_t_meet : 1 / v_v = (d - 1) / v_t )
    (h_v_s_speed : 18 / v_v = 18 / v_s + 1.4) (h_v_t_speed : v_t = 6 * v_v) :
    v_v = 10 ∧ v_s = 45 ∧ v_t = 60 := by 
  obtain ⟨h_v_s, h_v_t, h_v_v⟩ := h_v
  rw [h_v_t_speed] at h_v_t_meet 
  have h5 : v_v ≠ 0 := by nlinarith 
  have helper_eq : 6 * (1 : ℝ) = d - 1 := by 
    field_simp at h_v_t_meet
    nlinarith [h5, h_v_t_speed]
  have h2 : d = 7 := by 
    nlinarith [helper_eq]
  have h4 : v_s = 105 - 6 * v_v := by
    have h1 : v_s + v_t = 105 := by
      have eq1 : v_s * (4 / 60) + v_t * (4 / 60) = d := h_s_t_meet
      rw [h2] at eq1
      nlinarith 
    have h5 : v_t = 6 * v_v := h_v_t_speed
    linarith  
  have h3 : (18 / v_v : ℝ) = (18 / v_s + 1.4 : ℝ) := by linarith [h_v_s_speed]
  rw [h4] at h3
  -- Clear the denominator to convert to polynomial equations
  have h7 : v_v ≠ 0 := h5 
  have h8 : (105 - 6 * v_v : ℝ) ≠ 0 := by 
    nlinarith [h_v_s]
  field_simp [h7, h8] at h3 
  ring_nf at h3 
  have h11 : (v_v - 10) * (v_v - 15.5 : ℝ) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.1 h11) with h12 h12
  · -- v_v = 10 
    have h7 : v_v = 10 := by linarith 
    have h8 : v_s = 45 := by
      linarith [h4, h7]
    have h9 : v_t = 60 := by
      linarith [h7, h_v_t_speed]
    exact ⟨h7, h8, h9⟩
  · -- v_v = 15.5 
    have h7 : v_v = 15.5 := by linarith 
    have h8 : v_s = (105 - 6 * v_v : ℝ) := by linarith [h4]
    -- Show contradiction with h_v_s > 0
    have h9 : v_s < 0 := by
      rw [h7] at h8
      nlinarith 
    nlinarith [show v_s > 0 by linarith [h_v_s]]