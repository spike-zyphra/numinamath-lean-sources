import Mathlib

open Real Set

lemma arctan2inv_pos : 0 < arctan 2⁻¹ := by norm_num [Real.arctan_eq_arcsin]

lemma arctan2inv_lt_pi_div_four : arctan 2⁻¹ < π / 4 := by
  have : π / 4 - arctan 2⁻¹ = arctan 2⁻¹ - arctan 7⁻¹ := by linarith [Real.two_mul_arctan_inv_2_sub_arctan_inv_7]
  have h' : 0 < arctan 2⁻¹ - arctan 7⁻¹ := by linarith [Real.arctan_strictMono (show 7⁻¹ < 2⁻¹ by norm_num)]
  rw [← this] at h'
  linarith

theorem algebra_9233 (f : ℝ → ℝ)
  (h₀ : f = fun x ↦ cos x ^ 2 / (cos x * sin x - sin x ^ 2)) :
  IsLeast {y | ∃ x, 0 < x ∧ x < π/4 ∧ f x = y} 4 := by
  constructor
  · -- Show there exist x in (0,π/4) such that f x =4
    use arctan 2⁻¹
    constructor
    · -- Show 0 < arctan 2⁻¹
      linarith [arctan2inv_pos]
    constructor
    · -- Show arctan 2⁻¹ < π/4
      linarith [arctan2inv_lt_pi_div_four]
    · -- Show f (arctan2⁻¹) = 4
      rw [h₀]
      simp [Real.cos_arctan, Real.sin_arctan]
      <;> field_simp <;> norm_num
      <;> ring_nf <;> field_simp <;> norm_num
  · -- Show that 4 is the least element in {y | ∃ x, 0 < x ∧ x < π/4 ∧ f x = y}
    rintro y ⟨x, hx₁, hx₂, hfx⟩
    rw [h₀] at hfx
    simp at hfx
    have h3 : 0 < sin x := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h4 : 0 < cos x := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_pos, hx₁, hx₂]
    have h5 : cos x - sin x > 0 := by
      have h6 : cos x > sin x := by
        have h7 : cos x > cos (Real.pi / 4) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [Real.pi_pos, hx₁, hx₂]
        have h8 : cos (Real.pi / 4) = sin (Real.pi / 4) := by
          rw [Real.cos_pi_div_four]
          rw [Real.sin_pi_div_four]
          all_goals norm_num
        have h9 : sin (Real.pi / 4) > sin x := by 
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [Real.pi_pos, hx₁, hx₂]
        have h10 : cos x > sin x := by
          linarith [h7, h8, h9]
        linarith
      linarith
    have h10 : cos x * sin x - sin x ^ 2 > 0 := by
      have h11 : sin x > 0 := h3
      have h12 : cos x - sin x > 0 := h5
      nlinarith
    have h14 : cos x ^ 2 ≥ 4 * (cos x * sin x - sin x ^ 2) := by
      nlinarith [sq_nonneg (cos x - 2 * sin x)]
    have h15 : y ≥ 4 := by
      have h16 : y = cos x ^ 2 / (cos x * sin x - sin x ^ 2) := by
        field_simp [h10] at hfx ⊢
        nlinarith
      rw [h16]
      have h17 : cos x ^ 2 - 4 * (cos x * sin x - sin x ^ 2) ≥ 0 := by 
        nlinarith [sq_nonneg (cos x - 2 * sin x)]
      have h18 : cos x ^ 2 / (cos x * sin x - sin x ^ 2) - 4 ≥ 0 := by
        have h19 : cos x * sin x - sin x ^ 2 > 0 := h10
        have h20 : cos x ^ 2 - 4 * (cos x * sin x - sin x ^ 2) ≥ 0 := h17
        have h21 : (cos x ^ 2 - 4 * (cos x * sin x - sin x ^ 2)) / (cos x * sin x - sin x ^ 2) ≥ 0 := by
          apply div_nonneg
          linarith
          linarith
        have h22 : cos x ^ 2 / (cos x * sin x - sin x ^ 2) - 4 = 
          (cos x ^ 2 - 4 * (cos x * sin x - sin x ^ 2)) / (cos x * sin x - sin x ^ 2) := by 
          field_simp [h10]
          <;> ring_nf <;> field_simp [h10] <;> ring
        linarith
      linarith
    linarith