import Mathlib

theorem algebra_13376 {α β : ℝ} (hroots : α^2-8*α+5=0 ∧ β^2-8*β+5=0) (hα : α>β) :
    α-β=2*√11 := by
  have h₁ : α^2 - 8 * α + 5 = 0 := hroots.1
  have h₂ : β^2 - 8 * β + 5 = 0 := hroots.2
  have h3 : (α - β) * (α + β - 8) = 0 := by
    ring_nf at *
    nlinarith 
  have h4 : α - β ≠ 0 := by linarith
  have h5 : α + β - 8 = 0 := by 
    apply_fun (fun x => x / (α - β)) at h3
    field_simp [show α - β ≠ 0 by linarith] at h3
    linarith
  have h6 : α + β = 8 := by linarith 
  have h7 : α * β = 5 := by
    nlinarith [h₁, h₂, h6] 
  have h8 : (α - β) ^ 2 = 44 := by 
    nlinarith [h6, h7] 
  have h9 : α - β > 0 := by linarith 
  have h10 : α - β = Real.sqrt 44 := by 
    have h11 : (α - β) ^ 2 = 44 := h8 
    have h12 : 0 ≤ Real.sqrt 44 := Real.sqrt_nonneg 44 
    have h13 : Real.sqrt ((α - β) ^ 2) = Real.sqrt 44 := by 
      rw [h11] 
    have h14 : Real.sqrt ((α - β) ^ 2) = (α - β) := by 
      apply Real.sqrt_sq 
      linarith 
    linarith 
  have h14 : Real.sqrt 44 = 2 * Real.sqrt 11 := by 
    calc 
      Real.sqrt 44 = Real.sqrt (2^2 * 11) := by norm_num 
      _ = (Real.sqrt (2^2)) * Real.sqrt 11 := by rw [Real.sqrt_mul (by norm_num)]
      _ = (2) * Real.sqrt 11 := by rw [Real.sqrt_sq (by norm_num)]
      _ = 2 * Real.sqrt 11 := by ring 
  rw [h14] at h10 
  linarith