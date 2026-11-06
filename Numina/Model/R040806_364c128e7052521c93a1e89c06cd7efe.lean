import Mathlib

theorem algebra_185489 (α : ℝ) (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    ((Real.sqrt (Real.tan α) + Real.sqrt (1 / Real.tan α)) / (Real.sin α + Real.cos α))^2 =
    2 / Real.sin (2 * α) := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < Real.sin α := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : 0 < Real.cos α := by
    have h5 : α < Real.pi / 2 := h2
    have h6 : Real.cos α > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    linarith
  have htan : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]
  have h5 : Real.sqrt (Real.tan α) = Real.sqrt (Real.sin α) / Real.sqrt (Real.cos α) := by
    rw [htan]
    have h7 : 0 < Real.cos α := h4
    field_simp [Real.sqrt_div]
    all_goals
      try linarith
      try positivity
  have htan_pos : 0 < Real.tan α := by
    rw [htan]
    apply div_pos
    · linarith
    · linarith
  have h7 : 0 < (1 / Real.tan α : ℝ) := by
    positivity
  have h6 : Real.sqrt (1 / Real.tan α) = Real.sqrt (Real.cos α) / Real.sqrt (Real.sin α) := by
    have htan_eq : Real.tan α = Real.sin α / Real.cos α := by
      rw [Real.tan_eq_sin_div_cos]
    have htan_pos' : Real.tan α > 0 := htan_pos
    have h11 : 1 / Real.tan α = Real.cos α / Real.sin α := by
      rw [htan_eq]
      field_simp [h3.ne.symm]
      <;> linarith
    rw [h11]
    have h9 : 0 < Real.sin α := h3
    have h10 : 0 < Real.cos α := h4
    have h11 : Real.sqrt (Real.cos α / Real.sin α) = Real.sqrt (Real.cos α) / Real.sqrt (Real.sin α) := by
      rw [Real.sqrt_div (by linarith)]
      all_goals positivity
    rw [h11]
    all_goals positivity
  have h12 : Real.sqrt (Real.tan α) + Real.sqrt (1 / Real.tan α) = (Real.sin α + Real.cos α) / (Real.sqrt (Real.sin α) * Real.sqrt (Real.cos α)) := by
    rw [h5, h6]
    have h7 : 0 < Real.sin α := h3
    have h8 : 0 < Real.cos α := h4
    have h9 : 0 < Real.sqrt (Real.sin α) := by positivity
    have h10 : 0 < Real.sqrt (Real.cos α) := by positivity
    have h11 : Real.sqrt (Real.sin α) * Real.sqrt (Real.cos α) > 0 := by positivity
    field_simp [h9, h10, Real.mul_self_sqrt (show 0 ≤ Real.sin α by linarith), Real.mul_self_sqrt (show 0 ≤ Real.cos α by linarith)]
    <;> ring_nf
    <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg (Real.sin α), Real.sqrt_nonneg (Real.cos α), Real.sq_sqrt (show (0 : ℝ) ≤ Real.sin α by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ Real.cos α by linarith)]
  have eq1 : ((Real.sqrt (Real.tan α) + Real.sqrt (1 / Real.tan α)) / (Real.sin α + Real.cos α)) = 1 / (Real.sqrt (Real.sin α) * Real.sqrt (Real.cos α)) := by
    rw [show Real.sqrt (Real.tan α) + Real.sqrt (1 / Real.tan α) = (Real.sin α + Real.cos α) / (Real.sqrt (Real.sin α) * Real.sqrt (Real.cos α)) by linarith [h12]]
    have h14 : Real.sin α + Real.cos α > 0 := by positivity
    field_simp [h14, show Real.sqrt (Real.sin α) * Real.sqrt (Real.cos α) > 0 by positivity]
    <;> ring_nf <;> field_simp <;> ring_nf <;> norm_num
    all_goals nlinarith
  have eq2 : ((Real.sqrt (Real.tan α) + Real.sqrt (1 / Real.tan α)) / (Real.sin α + Real.cos α))^2 = 1 / (Real.sin α * Real.cos α) := by
    rw [eq1]
    have h10 : (Real.sqrt (Real.sin α) * Real.sqrt (Real.cos α)) ^ 2 = Real.sin α * Real.cos α := by
      calc
        (Real.sqrt (Real.sin α) * Real.sqrt (Real.cos α)) ^ 2
          = (Real.sqrt (Real.sin α) ^ 2) * (Real.sqrt (Real.cos α) ^ 2) := by ring
        _ = Real.sin α * Real.cos α := by
          rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
          <;> linarith
    have h11 : Real.sin α * Real.cos α > 0 := by positivity
    field_simp [h10, h11]
    <;> ring_nf <;> norm_num
    all_goals nlinarith
  have eq3 : 1 / (Real.sin α * Real.cos α) = 2 / Real.sin (2 * α) := by
    have htan2 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
      rw [show 2 * α = 2 * α by rfl]
      rw [Real.sin_two_mul]
    rw [htan2]
    have h17 : Real.sin α * Real.cos α > 0 := by positivity
    field_simp [show 2 * Real.sin α * Real.cos α > 0 by positivity, h17]
    <;> ring_nf <;> norm_num
    all_goals nlinarith
  rw [eq2]
  rw [eq3]