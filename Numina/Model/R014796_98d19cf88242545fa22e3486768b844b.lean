import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_151493 (f g : ℝ → ℝ)
  (hf : f = λ x => x^3) (hg : g = λ x => sqrt x) :
  ∫ x in (0)..(1), π * (g x)^2 - π * (f x)^2 = 5 * π / 14 := by
  simp_rw [hf, hg]
  have h1 : ∫ x in (0)..(1), π * (√x) ^ 2 - π * (x ^ 3) ^ 2 = 5 * π / 14 := by
    have h5 : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 → π * (√x) ^ 2 - π * (x ^ 3) ^ 2 = π * (x - x ^ 6) := by
      intro x hx
      have hx2 : (√x) ^ 2 = x := by
        rw [Real.sq_sqrt]
        linarith [hx.1]
      have hx3 : (x ^ 3) ^ 2 = x ^ 6 := by
        ring
      simp [hx2, hx3]
      <;> ring
    have h6 : ∫ x in (0)..(1), π * (√x) ^ 2 - π * (x ^ 3) ^ 2 =
        ∫ x in (0)..(1), π * (x - x ^ 6) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx_in_Icc : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa using hx
      exact h5 x hx_in_Icc
    rw [h6]
    simp [intervalIntegral.integral_const, mul_comm]
    all_goals
      ring_nf
      <;> norm_num
      <;> norm_num [Real.pi_pos]
      all_goals
        linarith [Real.pi_pos]
    all_goals 
      linarith [Real.pi_pos]
  exact h1