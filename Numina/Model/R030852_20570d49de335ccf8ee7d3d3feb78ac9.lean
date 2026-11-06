import Mathlib

theorem algebra_611101 :
  -- The emptying time T is:
  9 * Real.pi / 2 = ∫ h : ℝ in (0:ℝ)..(12:ℝ), (Real.pi * h / 16) := by

  have h1 : ∫ h : ℝ in (0:ℝ)..(12:ℝ), (Real.pi * h / 16) = 9 * Real.pi / 2 := by
    norm_num [intervalIntegral.integral_const, mul_comm]
    <;> ring_nf <;> norm_num
    all_goals 
      norm_num
  exact_mod_cast h1.symm