import Mathlib

theorem algebra_18843 (z1 z2 z3 : ℂ) (h₁ : ‖z1‖ = 1) (h₂ : ‖z2‖ = 2) (h₃ : ‖z3‖ = 3)
    (h₄ : ‖9 * z1 * z2 + 4 * z1 * z3 + z2 * z3‖ = 12) :
    ‖z1 + z2 + z3‖ = 2 := by
  have h1 := Complex.mul_conj z1
  have h2 := Complex.mul_conj z2
  have h3 := Complex.mul_conj z3

  have g1 : Complex.normSq z1 = ‖z1‖ ^ 2:= by exact Complex.normSq_eq_norm_sq z1
  have g2 : Complex.normSq z2 = ‖z2‖ ^ 2:= by exact Complex.normSq_eq_norm_sq z2
  have g3 : Complex.normSq z3 = ‖z3‖ ^ 2:= by exact Complex.normSq_eq_norm_sq z3

  rw [g1] at h1
  rw [g2] at h2
  rw [g3] at h3

  rw [h₁] at h1
  rw [h₂] at h2
  rw [h₃] at h3
  norm_num at h1 h2 h3

  rw [show z2 * z3 = 1 * z2 * z3 by simp] at h₄
  rw [←h1, ←h2, ←h3] at h₄

  rw [show z3 * (starRingEnd ℂ) z3 * z1 * z2 = (starRingEnd ℂ) z3 * z1 * z2 * z3 by ring] at h₄
  rw [show z2 * (starRingEnd ℂ) z2 * z1 * z3 = (starRingEnd ℂ) z2 * z1 * z2 * z3 by ring] at h₄
  rw [show z1 * (starRingEnd ℂ) z1 * z2 * z3 = (starRingEnd ℂ) z1 * z1 * z2 * z3 by ring] at h₄

  rw [show (starRingEnd ℂ) z3 * z1 * z2 * z3 + (starRingEnd ℂ) z2 * z1 * z2 * z3 + (starRingEnd ℂ) z1 * z1 * z2 * z3 = ((starRingEnd ℂ) z1 + (starRingEnd ℂ) z2 + (starRingEnd ℂ) z3) * (z1 * z2 * z3) by ring] at h₄

  have h4 : ‖((starRingEnd ℂ) z1 + (starRingEnd ℂ) z2 + (starRingEnd ℂ) z3) * (z1 * z2 * z3)‖ = ‖((starRingEnd ℂ) z1 + (starRingEnd ℂ) z2 + (starRingEnd ℂ) z3)‖ * ‖z1 * z2 * z3‖:= NormedField.norm_mul' ((starRingEnd ℂ) z1 + (starRingEnd ℂ) z2 + (starRingEnd ℂ) z3) (z1 * z2 * z3)
  rw [h4] at h₄

  have h5 : ‖z1 * z2 * z3‖ = ‖z1 * z2‖ * ‖z3‖:= NormedField.norm_mul' (z1 * z2) z3
  have h6 : ‖z1 * z2‖ = ‖z1‖ * ‖z2‖:= NormedField.norm_mul' z1 z2
  rw [h5, h6] at h₄
  norm_num [h₁, h₂, h₃] at h₄ 
  simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq] at h₁ h₂ h₃ h₄ ⊢
  ring_nf at h₁ h₂ h₃ h₄ ⊢
  nlinarith [sq_nonneg (z1.re), sq_nonneg (z1.im), sq_nonneg (z2.re), sq_nonneg (z2.im), sq_nonneg (z3.re), sq_nonneg (z3.im)]