import Mathlib

open Real Set
open scoped BigOperators
/-let the function f(x)=Asin(ω * x + φ)(A≠ 0,ω>0,0<φ<π/2),if f(5π/6)+f(0)=0, then
the minimum value of ω is 6/5-/
theorem algebra_280506 {A ω φ : ℝ} (hA : A ≠ 0) (hω : ω > 0)
  (hφ : 0 < φ ∧ φ < π / 2) (f : ℝ → ℝ) (hf : f = λ x => A * sin (ω * x + φ))
  (h : f (5 * π / 6) + f 0 = 0) :
  ω ≥ 6 / 5 := by
    rw [hf] at h
    simp at h
   -- prove step by step
    have h1 : A * sin (ω * (5 * π / 6) + φ) + A * sin φ = 0 := by
      simpa using h
    have h2 : A ≠ 0 := hA
    have h3 : sin (ω * (5 * π / 6) + φ) + sin φ = 0 := by
      apply (mul_left_inj' h2).mp
      linarith
    have h4 : sin (ω * (5 * π / 6) + φ) + sin φ = 0 := h3
    have h5 : sin (ω * (5 * π / 6) + φ) = - sin φ := by linarith
    have h6 : 0 < φ := hφ.left
    have h7 : φ < π / 2 := hφ.right
    have h8 : 0 < sin φ := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    have h9 : sin (ω * (5 * π / 6) + φ) < 0 := by linarith [h5, h8]
    by_contra h10
    push_neg at h10
    have h13 : ω * (5 * π / 6) < π := by
      nlinarith [h10, Real.pi_pos]
    have h14 : 0 < ω * (5 * π / 6) := by
      nlinarith [hω, Real.pi_pos]
    have h15 : 0 < sin (ω * (5 * π / 6)) := by
      apply sin_pos_of_pos_of_lt_pi
      · nlinarith [Real.pi_pos, h14]
      · nlinarith [Real.pi_pos, h13]
    have h16 : -1 < cos (ω * (5 * π / 6)) := by
      have h17 : ω * (5 * π / 6) < π := h13
      have h18 : cos (ω * (5 * π / 6)) > -1 := by
        have h19 : ω * (5 * π / 6) < π := h13
        have h20 : ω * (5 * π / 6) ≥ 0 := by nlinarith [Real.pi_pos, hω]
        have h21 : cos (ω * (5 * π / 6)) > -1 := by
          have hcos : cos (ω * (5 * π / 6)) > cos π := by
            apply Real.cos_lt_cos_of_nonneg_of_le_pi
            all_goals linarith
          rw [Real.cos_pi] at hcos
          linarith
        linarith
      linarith
    have h19 : cos φ > 0 := by
      have h20 : φ < π / 2 := h7
      have h21 : cos φ > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · -- Show φ > -π/2
          linarith [h6]
        · -- Show φ < π/2
          linarith [h20]
      linarith
    have h22 : sin (ω * (5 * π / 6)) * cos φ + cos (ω * (5 * π / 6)) * sin φ = - sin φ := by
      have h23 : sin (ω * (5 * π / 6) + φ) = sin (ω * (5 * π / 6)) * cos φ + cos (ω * (5 * π / 6)) * sin φ := by
        rw [sin_add]
      rw [h23] at h5
      linarith
    have h24 : sin (ω * (5 * π / 6)) * cos φ + (cos (ω * (5 * π / 6)) + 1) * sin φ = 0 := by
      linarith [h22, h8]
    have h25 : sin (ω * (5 * π / 6)) * cos φ > 0 := by
      apply mul_pos
      · linarith [h15]
      · linarith [h19]
    have h26 : (cos (ω * (5 * π / 6)) + 1) * sin φ > 0 := by
      apply mul_pos
      · linarith [h16]
      · linarith [h8]
    have h27 : sin (ω * (5 * π / 6)) * cos φ + (cos (ω * (5 * π / 6)) + 1) * sin φ > 0 := by
      linarith [h25, h26]
    linarith [h24, h27]