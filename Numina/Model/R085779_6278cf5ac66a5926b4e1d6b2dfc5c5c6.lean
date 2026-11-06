import Mathlib

open Real Set
open scoped Real

theorem algebra_132538 (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    sin (4 * arcsin x) = 4 * x * (1 - 2 * x^2) * sqrt (1 - x^2) := by 
  rw [mem_Icc] at hx
  rcases hx with ⟨hx1, hx2⟩
  have h2 : sin (arcsin x) = x := by 
    apply sin_arcsin 
    all_goals linarith 
  have h3 : cos (arcsin x) = Real.sqrt (1 - x^2) := by 
    rw [cos_arcsin]
    all_goals nlinarith 
  have h4 : sin (2 * arcsin x) = 2 * x * Real.sqrt (1 - x^2) := by 
    rw [sin_two_mul]
    rw [h2, h3]
    all_goals nlinarith 
  have h5 : cos (2 * arcsin x) = 1 - 2 * x^2 := by 
    have h7 : cos (2 * arcsin x) = 1 - 2 * (sin (arcsin x))^2 := by 
      rw [cos_two_mul, sin_sq]
      <;> ring_nf <;> simp [sq]
      <;> ring 
    rw [h7, h2]
    all_goals nlinarith
  have h6 : sin (4 * arcsin x) = 2 * sin (2 * arcsin x) * cos (2 * arcsin x) := by 
    rw [show 4 * arcsin x = 2 * (2 * arcsin x) by ring]
    rw [sin_two_mul]
    all_goals ring_nf <;> simp [mul_assoc]
    <;> ring
  rw [h6, h4, h5]
  all_goals 
    ring_nf <;> simp [Real.sqrt_mul_self, hx1, hx2]
    <;> ring_nf <;> nlinarith