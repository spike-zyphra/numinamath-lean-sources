import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_107708 (f : ℝ → ℝ) (hf : f = λ x => (sin x) ^ (cos x)) :
    IsGreatest (image f (Icc 0 (π/2))) 1 := by 
  constructor
  · -- Show that 1 belongs to the image of f on [0, π/2]
    use Real.pi / 2
    constructor 
    · -- Show that π/2 is in the interval [0, π/2]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Compute f(π/2) and show it equals 1
      rw [hf]
      have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have h2 : cos (Real.pi / 2) = 0 := by 
        rw [Real.cos_pi_div_two]
      simp [h1, h2]
  · -- Show that 1 is an upper bound for the image of f on [0, π/2]
    intro y hy 
    rcases hy with ⟨x, hx, hfx⟩ 
    have hx1 : 0 ≤ x := by 
      have h1 : x ∈ Icc (0 : ℝ) (Real.pi / 2) := hx 
      exact h1.left 
    have hx2 : x ≤ Real.pi / 2 := by 
      have h2 : x ∈ Icc (0 : ℝ) (Real.pi / 2) := hx 
      exact h2.right 
    rw [hf] at hfx
    have h1 : sin x ≥ 0 := by 
      apply sin_nonneg_of_nonneg_of_le_pi 
      · linarith [Real.pi_pos, hx1] 
      · linarith [Real.pi_pos, hx2] 
    have h2 : cos x ≥ 0 := by 
      apply cos_nonneg_of_neg_pi_div_two_le_of_le 
      all_goals 
        linarith [Real.pi_pos, hx1, hx2] 
    have h3 : sin x ≤ 1 := by 
      apply sin_le_one 
    have h5 : sin x ^ cos x ≤ 1 := by 
      have h7 : sin x ^ cos x ≤ (1 : ℝ) ^ cos x := by 
        apply Real.rpow_le_rpow
        all_goals 
          linarith [h1, h3, h2]
      have h8 : (1 : ℝ) ^ cos x = 1 := by 
        simp 
      have h9 : sin x ^ cos x ≤ 1 := by 
        linarith [h7, h8] 
      linarith 
    have h6 : (fun (y : ℝ) => sin y ^ cos y) x = sin x ^ cos x := by 
      simp 
    have eq1 : sin x ^ cos x = y := by 
      linarith [hfx, h6]
    linarith [eq1, h5]