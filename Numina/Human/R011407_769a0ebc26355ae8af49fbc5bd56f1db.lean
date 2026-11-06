import Mathlib

open Real
/-
3A. Solve the equation

$$
\sqrt{1+3 \sin ^{3} x}=3-\sqrt{1-\cos ^{4} x}
$$
-/

theorem algebra_251156:
0 ≤ 1 + 3 * (sin x)^3 ∧ 
0 ≤ 1 - (cos x)^4 ∧ 
sqrt (1 + 3 * (sin x)^3) = 3 - sqrt (1 - (cos x)^4) 
↔ 
(∃ k:ℤ, π/2 + k * (2 * π) = x) := by

  constructor

  --From left to right.
  intro h
  obtain ⟨spos, cpos, h⟩ := h
  
  --We prove that sin x = 1. Then the claim follows directly.
  --This claim follows from the fact that sin x and cos x are between -1 and 1.
  have sinxe : sin x = 1 := by 
    have t1 : sqrt (1 + 3 * (sin x)^3) ≤ 2 := by 
      have l1: (1 + 3 * (sin x)^3) ≤ 4 := by 
        have : (sin x)^3 ≤ 1 := by 
          have : sin x ≤ 1 := by exact sin_le_one x
          by_cases sinneg : sin x < 0
          have : (sin x)^3 < 0 := by refine Odd.pow_neg ?_ sinneg; use 1; simp
          linarith
          have sinnneg : 0 ≤ sin x := by linarith
          exact pow_le_one₀ sinnneg this
        linarith
      refine sqrt_le_iff.mpr ?_
      simp
      have : (2:ℝ)^2 = 4 := by norm_num
      rw [←this] at l1
      exact l1
    have t2 : 2 ≤ 3 - sqrt (1 - (cos x)^4) := by 
      have l1 : sqrt (1 - (cos x)^4) ≤ 1 := by
        have : (1 - (cos x)^4) ≤ 1 := by 
          have : 0 ≤ (cos x)^4 := by positivity
          linarith
        exact sqrt_le_one.mpr this
      linarith
    have t3 : sqrt (1 + 3 * (sin x)^3) = 2 := by linarith
    have t4 : (1 + 3 * (sin x)^3) = 4 := by 
      have l1: (sqrt (1 + 3 * (sin x)^3))^2 = 2^2 := by exact congrFun (congrArg HPow.hPow t3) 2
      have l2: (sqrt (1 + 3 * (sin x)^3))^2 = (1 + 3 * (sin x)^3) := by exact sq_sqrt spos
      rw [l2] at l1
      have : (2:ℝ)^2 = 4 := by norm_num
      rw [this] at l1
      exact l1
    have t5 : (sin x)^3 = 1 := by linarith
    have t6 : (sin x) = 1 := by 
      rw [pow_eq_one_iff_cases] at t5
      have : ¬ Even 3 := by decide
      simp [this] at t5
      exact t5
    exact t6
  rw [Real.sin_eq_one_iff] at sinxe
  exact sinxe


  --For the other direction, simple calculation.
  intro xe
  have sinxe : sin x = 1 := by
    rw [← Real.sin_eq_one_iff] at xe
    exact xe
  have cosxe : cos x = 0 := by
    have : ∃ (l : ℤ), x = (2 * ↑l + 1) * Real.pi / 2 := by 
      obtain ⟨k,hk⟩ := xe
      use (2*k)
      rw [← hk]
      field_simp
      ring_nf
    rw [← Real.cos_eq_zero_iff] at this
    exact this
  simp [sinxe,cosxe]
  norm_num
  refine sqrt_eq_cases.mpr ?_
  simp
  norm_num