import Mathlib

theorem algebra_306662 (α β : ℝ) (h₀ : Real.sin (α + 2 * β) / Real.sin α = 3)
    (h₁ : ¬∃ k : ℤ, β = k / 2 * Real.pi) (h₂ : ¬∃ n : ℤ, α + β = n * Real.pi + Real.pi / 2) :
    Real.tan (α + β) / Real.tan β = 2 := by 
  have h4 : Real.sin α ≠ 0 := by 
    by_contra h
    have h5 : Real.sin (α + 2 * β) / Real.sin α = 0 := by 
      simp [h]
    linarith
  have h12 : Real.sin β ≠ 0 := by
    by_contra h0
    have : ∃ k : ℤ, β = k / 2 * Real.pi := by 
      have h14 : Real.sin β = 0 := by linarith [h0]
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h14
      refine ⟨(2 * k), by 
        rw [show (↑(2 * k) : ℝ) / 2 * Real.pi = (k : ℝ) * Real.pi by
          field_simp
          <;> nlinarith
        ] at *
        <;> linarith [Real.pi_pos]
      ⟩
    contradiction
  have hcosβ : Real.cos β ≠ 0 := by
    by_contra h3
    have h15 : ∃ k : ℤ, β = k / 2 * Real.pi := by 
      have h17 : Real.cos β = 0 := by linarith
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 h17
      refine ⟨(2 * k + 1), by
        -- Transform formula.
        rw [show (↑(2 * k + 1) : ℝ) / 2 * Real.pi = (k : ℝ) * Real.pi + Real.pi / 2 by
          field_simp
          <;> ring
        ] at *
        <;> linarith [Real.pi_pos]
      ⟩
    contradiction
  have hcosαβ : Real.cos (α + β) ≠ 0 := by 
    by_contra h13
    have h18 : ∃ n : ℤ, α + β = n * Real.pi + Real.pi / 2 := by 
      have h14 : Real.cos (α + β) = 0 := by linarith
      obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.1 h14
      refine ⟨n, by linarith⟩
    contradiction
  have h5 : Real.sin (α + 2 * β) = 3 * Real.sin α := by 
    have h6 : Real.sin α ≠ 0 := h4
    have h7 : Real.sin (α + 2 * β) / Real.sin α = 3 := h₀
    have h8 : Real.sin (α + 2 * β) = 3 * Real.sin α := by
      have eq1 : Real.sin (α + 2 * β) / Real.sin α = 3 := h₀
      have h6 : Real.sin α ≠ 0 := by assumption
      field_simp [h6] at eq1 ⊢
      linarith [eq1]
    exact h8
  have h6 : Real.sin (α + 2 * β) = Real.sin (α + β) * Real.cos β + Real.cos (α + β) * Real.sin β := by 
    rw [show α + 2 * β = (α + β) + β by ring]
    rw [Real.sin_add]
  have h7 : Real.sin α = Real.sin (α + β) * Real.cos β - Real.cos (α + β) * Real.sin β := by 
    have h8 : Real.sin α = Real.sin ((α + β) - β) := by ring_nf
    rw [h8]
    rw [Real.sin_sub]
  rw [h6] at h5
  rw [h7] at h5
  have heq : Real.sin (α + β) * Real.cos β = 2 * Real.cos (α + β) * Real.sin β := by 
    linarith 
  have ht1 : Real.tan (α + β) = Real.sin (α + β) / Real.cos (α + β) := by 
    rw [Real.tan_eq_sin_div_cos]
  have ht2 : Real.tan β = Real.sin β / Real.cos β := by 
    rw [Real.tan_eq_sin_div_cos]
  have h14 : Real.tan (α + β) = 2 * Real.tan β := by 
    rw [ht1, ht2]
    have heq' : Real.sin (α + β) * Real.cos β = 2 * Real.cos (α + β) * Real.sin β := heq
    have h15 : Real.cos (α + β) ≠ 0 := hcosαβ
    have h16 : Real.cos β ≠ 0 := hcosβ
    field_simp [h15, h16] at heq' ⊢
    linarith 
  have htan2 : Real.tan β ≠ 0 := by
    by_contra h0
    have h0 : Real.tan β = 0 := by linarith 
    rw [ht2] at h0 
    have hsinβ : Real.sin β = 0 := by 
      field_simp [hcosβ] at h0 ⊢
      all_goals linarith
    contradiction
  rw [h14]
  field_simp [htan2]
  <;> linarith