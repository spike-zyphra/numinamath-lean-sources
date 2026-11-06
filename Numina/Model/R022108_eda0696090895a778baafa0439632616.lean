import Mathlib

open Real Set
open scoped Real

theorem algebra_12848 (α : ℝ) (f : ℝ → ℝ)
  (hf : ∀ x, f x = (sin (x + α) + sin (x - α) - 4 * sin x) / (cos (x + α) + cos (x - α) - 4 * cos x)) :
  ∀ x ∈ Ioo 0 (π/4), 0 < f x ∧ f x < 1 := by 
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have hfx : f x = (sin (x + α) + sin (x - α) - 4 * sin x) / (cos (x + α) + cos (x - α) - 4 * cos x) := hf x
  have h1 : sin (x + α) + sin (x - α) = 2 * sin x * cos α := by
    rw [sin_add, sin_sub]
    ring
  have h2 : cos (x + α) + cos (x - α) = 2 * cos x * cos α := by
    rw [cos_add, cos_sub]
    ring 
  -- Simplify `f(x)`
  have hfx2 : f x = sin x / cos x := by 
    rw [hfx]
    have eq1 : sin (x + α) + sin (x - α) - 4 * sin x = 2 * sin x * cos α - 4 * sin x := by
      linarith [h1]
    have eq2 : cos (x + α) + cos (x - α) - 4 * cos x = 2 * cos x * cos α - 4 * cos x := by 
      linarith [h2]
    rw [eq1, eq2]
    have eq3 : (2 * sin x * cos α - 4 * sin x) = 2 * sin x * (cos α - 2) := by ring
    have eq4 : (2 * cos x * cos α - 4 * cos x) = 2 * cos x * (cos α - 2) := by ring
    rw [eq3, eq4]
    have h3 : cos α - 2 ≠ 0 := by 
      have hcos : cos α ≤ 1 := cos_le_one α
      by_contra h 
      have : cos α = 2 := by linarith 
      nlinarith 
    have hcosx : cos x > 0 := by 
      apply cos_pos_of_mem_Ioo 
      constructor 
      · linarith [Real.pi_pos] 
      · linarith [Real.pi_pos]
    have h5 : cos α - 2 ≠ 0 := h3
    field_simp [show cos α - 2 ≠ 0 by exact h5, show cos x ≠ 0 by linarith]
    <;> ring
  -- Show `0 < f x` and `f x < 1`.
  have htan : 0 < sin x := by 
    apply sin_pos_of_pos_of_lt_pi 
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  -- Show `cos x > 0` for `x \in (0, \pi/4)` 
  have hcosx : cos x > 0 := by
    apply cos_pos_of_mem_Ioo 
    constructor 
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have htan2 : sin x / cos x > 0 := by 
    apply div_pos htan hcosx 
  -- Prove the goal.
  constructor 
  · -- Show 0 < f x 
    rw [hfx2]
    exact htan2 
  · -- Show f x < 1 
    rw [hfx2]
    have h4 : sin x < cos x := by
      have h17 : x < Real.pi / 4 := hx2
      have h18 : sin x < sin (Real.pi / 4) := by 
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two 
        all_goals nlinarith [Real.pi_pos, Real.pi_gt_three]
      have h19 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := sin_pi_div_four 
      have h20 : cos x > cos (Real.pi / 4) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi 
        all_goals nlinarith [Real.pi_pos, Real.pi_gt_three]
      have h21 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := cos_pi_div_four 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h6 : sin x / cos x < 1 := by
      have h5 : cos x > 0 := hcosx 
      have h7 : sin x < cos x := h4 
      have h8 : cos x > 0 := h5 
      have h9 : sin x / cos x < (cos x) / cos x := by 
        apply (div_lt_div_right h8).mpr 
        linarith 
      have h10 : (cos x) / cos x = 1 := by 
        field_simp 
      linarith [h9, h10]
    exact h6