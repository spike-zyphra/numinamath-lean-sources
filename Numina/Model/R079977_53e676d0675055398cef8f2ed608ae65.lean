import Mathlib

theorem algebra_288949 (α : Real) (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) (htan : Real.tan α = 2) :
    Real.sin α = 2 / Real.sqrt 5 ∧ Real.cos α = Real.sqrt 5 / 5 := by
  rcases hα with ⟨h1, h2⟩
  have h3 : Real.cos α ≠ 0 := by
    by_contra h
    have htan0 : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    rw [htan0] at htan
    norm_num at htan
  have htan' : Real.sin α = 2 * Real.cos α := by
    have htan_eq : Real.tan α = Real.sin α / Real.cos α := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan_eq] at htan
    have h4 : Real.cos α ≠ 0 := h3
    field_simp [h4] at htan ⊢
    nlinarith
  have hcos : Real.cos α = Real.sqrt 5 / 5 := by
    have hcos_sq : Real.cos α ^ 2 = 1 / 5 := by
      have hsin_sq : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      rw [htan'] at hsin_sq
      nlinarith
    have hcos_pos : 0 < Real.cos α := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have hcos_sqrt : Real.cos α = Real.sqrt (Real.cos α ^ 2) := by
      rw [Real.sqrt_sq]
      all_goals linarith
    rw [hcos_sqrt, hcos_sq]
    have h5 : Real.sqrt (1 / 5 : ℝ) = Real.sqrt 5 / 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h5]
    all_goals norm_num
  have hsin : Real.sin α = 2 / Real.sqrt 5 := by
    have hsin' : Real.sin α = 2 * Real.cos α := htan'
    rw [hsin']
    rw [hcos]
    field_simp
    <;> ring_nf <;> norm_num
    <;> ring
  constructor
  · exact hsin
  · exact hcos