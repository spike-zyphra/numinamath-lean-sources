import Mathlib

theorem algebra_302780 (α : ℝ) (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sqrt ((1 - Real.tan α / Real.sin α) ^ 2) = Real.tan α / Real.sin α - 1 := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : 0 < Real.sin α := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : 0 < Real.cos α := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    all_goals linarith [Real.pi_pos]
  -- Define tan α as sin α / cos α
  have htan : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]
  have htan2 : 0 < Real.tan α := by 
    rw [htan]
    apply div_pos
    exact h1
    exact h2
  -- Simplify tan α / sin α
  have h6 : Real.tan α / Real.sin α = 1 / Real.cos α := by
    rw [htan]
    have h7 : Real.sin α ≠ 0 := by linarith
    field_simp [h7]
    <;> linarith
  have h14 : Real.cos α < 1 := by
    have h12 : Real.cos α < Real.cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos]
    have h13 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    nlinarith
  -- Show that 1 - tan α / sin α < 0
  have h8 : 1 - Real.tan α / Real.sin α < 0 := by
    have htan2 : Real.tan α / Real.sin α > 1 := by 
      rw [h6]
      have h15 : Real.cos α > 0 := h2
      have h14 : Real.cos α < 1 := h14
      have h25 : (1 : ℝ) / Real.cos α > (1 : ℝ) := by
        have h23 : Real.cos α > 0 := h2
        have h24 : Real.cos α < 1 := h14
        apply (lt_div_iff₀' (by linarith)).mpr
        nlinarith
        all_goals linarith
      linarith
    linarith
  -- Calculate sqrt
  have h10 : Real.sqrt ((1 - Real.tan α / Real.sin α) ^ 2) = 
          abs (1 - Real.tan α / Real.sin α) := by
    rw [Real.sqrt_sq_eq_abs]
  -- Calculate abs
  have h11 : abs (1 - Real.tan α / Real.sin α) = Real.tan α / Real.sin α - 1 := by
    rw [abs_of_neg h8]
    all_goals
      linarith
  -- Final steps
  rw [h10, h11]
  all_goals
    linarith