import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_187364 (f : ℝ → ℝ) (hf : f = λ x => 2/3 * cos (3*x - π/6)) :
    IsGreatest (image f (Ioo 0 (π/2))) (2/3) ∧
    IsLeast (image f (Ioo 0 (π/2))) (-2/3) ∧
    f (π/18) = 2/3 ∧ f (7*π/18) = -2/3 := by 
  constructor
  · -- Need to prove that 2/3 is greatest in image.
    constructor 
    · -- Use point π / 18
      use π / 18
      constructor
      · -- Show that π / 18 is in interval
        have h1 : 0 < π / 18 := by
          linarith [Real.pi_pos]
        have h2 : π / 18 < π / 2 := by
          linarith [Real.pi_pos]
        exact ⟨h1, h2⟩
      · -- Calculate f(π / 18) = 2 / 3
        rw [hf]
        have h3 : 3 * (π / 18) - π / 6 = (0 : ℝ) := by
          linarith [Real.pi_pos]
        simp [h3]
        <;> field_simp <;> linarith 
    · -- Show that for any y in image, y ≤ 2/3
      intro y hy 
      rcases hy with ⟨x, hx, hfx⟩ 
      rw [hf] at hfx 
      simp at hfx 
      rcases hx with ⟨hx1, hx2⟩
      have h1 : -1 ≤ cos (3 * x - π / 6) ∧ cos (3 * x - π / 6) ≤ 1 := by
        apply cos_mem_Icc 
      nlinarith 
  constructor
  · -- Now prove -2/3 is the smallest in image 
    constructor 
    · -- Use 7π/18 
      use 7 * π / 18 
      constructor 
      · -- Show in interval 
        have h1 : 0 < 7 * π / 18 := by
          linarith [Real.pi_pos]
        have h2 : 7 * π / 18 < π / 2 := by
          linarith [Real.pi_pos]
        exact ⟨h1, h2⟩
      · -- Calculate f(7π/18) = -2/3 
        rw [hf]
        have h4 : 3 * (7 * π / 18) - π / 6 = Real.pi := by
          linarith [Real.pi_pos]
        simp [h4]
        <;> field_simp <;> linarith
    · -- Show that any y in image, -2/3 ≤ y
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩ 
      rw [hf] at hfx 
      simp at hfx
      rcases hx with ⟨hx1, hx2⟩ 
      have h1 : -1 ≤ cos (3 * x - π / 6) ∧ cos (3 * x - π / 6) ≤ 1 := by
        apply cos_mem_Icc 
      nlinarith 
  constructor
  · -- Prove f(π/18) = 2/3 
    rw [hf]
    have h3 : 3 * (π / 18) - π / 6 = (0 : ℝ) := by
      linarith [Real.pi_pos]
    simp [h3]
    <;> field_simp <;> linarith
  · -- Prove f(7π/18) = -2/3 
    rw [hf]
    have h4 : 3 * (7 * π / 18) - π / 6 = Real.pi := by
      linarith [Real.pi_pos]
    simp [h4]
    <;> field_simp <;> linarith