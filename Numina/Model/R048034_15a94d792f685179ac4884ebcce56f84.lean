import Mathlib

open Real Set
open scoped Real

theorem algebra_9092 {f : ℝ → ℝ}
  (hf : f = λ x => sqrt 2 * sin x * (cos x + sin x) - sqrt 2 / 2)
  (I : Set ℝ) (hI : I = Icc 0 (π/2)) :
  IsLeast (image f I) (-sqrt 2 / 2) := by
  rw [hI]
  constructor
  · -- Show that -sqrt 2 / 2 is in the image of f over I
    use 0
    constructor
    · -- Show that 0 is in Icc 0 (π/2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show that f(0) = -sqrt 2 / 2
      rw [hf]
      have h1 : (sqrt 2 * sin (0 : ℝ) * (cos (0 : ℝ) + sin (0 : ℝ)) - sqrt 2 / 2) = -sqrt 2 / 2 := by
        have h2 : sin (0 : ℝ) = (0 : ℝ) := by simp
        have h3 : cos (0 : ℝ) = (1 : ℝ) := by simp
        rw [h2, h3]
        all_goals ring_nf
      simpa using h1
  · -- Show that -sqrt 2 / 2 is the least
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : 0 ≤ x := by 
      have h1 : x ∈ Icc (0 : ℝ) (π / 2) := hx
      exact h1.left
    have hx2 : x ≤ π / 2 := by 
      have h1 : x ∈ Icc (0 : ℝ) (π / 2) := hx
      exact h1.right
    have h6 : 0 ≤ sin x := by 
      apply sin_nonneg_of_nonneg_of_le_pi 
      all_goals
        linarith [Real.pi_pos]
    have h7 : 0 ≤ cos x := by 
      apply cos_nonneg_of_neg_pi_div_two_le_of_le
      all_goals
        linarith [Real.pi_pos]
    have h8 : sin x + cos x ≥ 0 := by 
      linarith
    rw [hf] at hfx
    have h1 : sqrt 2 * sin x * (cos x + sin x) - sqrt 2 / 2 = y := by
      simpa using hfx
    have h5 : sqrt 2 * sin x * (cos x + sin x) - sqrt 2 / 2 ≥ -sqrt 2 / 2 := by
      have h9 : sqrt 2 * sin x * (cos x + sin x) ≥ 0 := by 
        have h14 : sin x ≥ 0 := h6 
        have h15 : cos x + sin x ≥ 0 := by linarith 
        have h16 : sqrt 2 ≥ 0 := by positivity 
        nlinarith [mul_nonneg (show sin x ≥ 0 by linarith) (show cos x + sin x ≥ 0 by linarith), Real.sqrt_nonneg 2, mul_nonneg (show sqrt 2 ≥ 0 by positivity) (show sin x ≥ 0 by linarith)]
      linarith
    linarith [h1, h5]