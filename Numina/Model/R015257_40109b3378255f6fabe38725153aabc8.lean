import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_151537 (f : ℝ → ℝ) (hf : f = λ x => cos x * sin x ^ 2) :
    ∫ x in (0)..(π/2), f x = 1/3 := by 
  rw [hf]
  have h1 : ∫ x in (0 : ℝ)..(π / 2), cos x * sin x ^ 2 = 1 / 3 := by
    have h2 : ∫ x in (0 : ℝ)..(π / 2), cos x * sin x ^ 2 = (∫ u in (0 : ℝ)..(1 : ℝ), u^2) := by
      have h3 : ∀ x : ℝ, cos x * sin x ^ 2 = (sin x) ^ 2 * cos x := by
        intro x
        ring_nf
      -- Use substitution $u = \sin x$. 
      -- Then $du = \cos x dx$.
      -- When $x = 0$, $u = 0$; when $x = \pi/2$, $u = 1$.
      -- So the integral becomes $\int_{0}^{1} u^2 du$.
      simp_rw [h3]
      -- Apply substitution rule for definite integral.
      norm_num
      <;> norm_num [Real.sin_pi_div_two]
      <;> try { 
          norm_num [Real.sin_pi_div_two]
          <;> norm_num [Real.sin_pi_div_two, Real.sin_zero]
          <;> try { tauto }
        }
      <;> try { 
          simp [intervalIntegral.integral_const, mul_assoc, mul_comm, mul_left_comm, Real.sin_pi_div_two]
          <;> ring_nf
          <;> norm_num [Real.sin_pi_div_two, Real.sin_zero]
          <;> try { tauto }
        }
      <;> try { 
          norm_num [Real.sin_pi_div_two]
          <;> norm_num [Real.sin_pi_div_two, Real.sin_zero]
          <;> try { tauto }
        }
      <;> try { 
          norm_num [Real.sin_zero, Real.sin_pi_div_two]
          <;> try { tauto }
        }
      all_goals 
        try { 
          norm_num [Real.sin_zero, Real.sin_pi_div_two]
          <;> try { tauto }
        }
      all_goals 
        try { 
          simp_all [Real.sin_pi_div_two, Real.sin_zero]
          <;> try { tauto }
        }
      <;> norm_num [Real.sin_zero, Real.sin_pi_div_two]
      <;> norm_num [Real.sin_zero, Real.sin_pi_div_two]
      <;> tauto
    rw [h2]
    norm_num
    <;> try norm_num
  exact h1