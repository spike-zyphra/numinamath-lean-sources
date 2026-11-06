import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_185138 {A ω : ℝ} (hA : A ≠ 0) (hω : ω ≠ 0)
  (x : ℝ → ℝ) (hx : x = λ t => A * sin (ω * t)) :
  deriv x (2 * π / ω) = A * ω * cos (ω * (2 * π / ω)) ∧
  iteratedDeriv 2 x (2 * π / ω) = -A * ω^2 * sin (ω * (2 * π / ω)) ∧
  ∀ t, iteratedDeriv 2 x t = -A * ω^2 * sin (ω * t) := by

  -- Establish deriv x
  have eq1 : deriv x = fun t => A * ω * cos (ω * t) := by 
    rw [hx]
    funext t 
    simp [deriv_mul, deriv_id'', mul_comm ω, differentiableAt_id', Real.differentiableAt_sin]
    all_goals ring_nf 
    <;> simp [mul_comm]
    <;> ring 
  -- Establish deriv (deriv x)
  have eq2 : deriv (deriv x) = fun t => -A * ω^2 * sin (ω * t) := by 
    rw [eq1]
    funext t 
    simp [deriv_mul, deriv_id'', mul_comm ω, differentiableAt_id', Real.differentiableAt_cos]
    all_goals ring_nf 
    <;> simp [mul_comm]
    <;> ring

  -- Now split the conjunction and prove each part
  constructor
  · -- First part: deriv x at t = 2π/ω
    rw [eq1]
    all_goals ring_nf
    all_goals field_simp 
    all_goals try norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two] 
    all_goals try linarith
    all_goals try norm_num
  constructor
  · -- Second part: iteratedDeriv 2 x at t = 2π/ω
    -- First establish what iteratedDeriv 2 x is
    have h3 : iteratedDeriv 2 x = deriv (deriv x) := by
      simp [iteratedDeriv_succ]
      <;> aesop 
      <;> aesop 
      all_goals try nlinarith 
      all_goals try norm_num
      all_goals try ring 
      all_goals try simp [mul_assoc]
      <;> try norm_num 
      <;> try tauto 
      all_goals try nlinarith 
      all_goals try tauto
    -- Calculate the value at t = 2 * π / ω
    rw [h3, eq2]
    all_goals simp [show ω * (2 * π / ω) = 2 * π by
      have h1 : ω ≠ 0 := hω 
      field_simp [h1]
      <;> ring_nf 
      all_goals field_simp
      all_goals norm_num 
      all_goals try linarith 
      all_goals try norm_num 
      all_goals try norm_num 
      all_goals try norm_num 
      all_goals try nlinarith 
      <;> try norm_num]
    all_goals norm_num [Real.sin_two_pi, Real.cos_two_pi] 
    all_goals try linarith 
    all_goals try norm_num 
    all_goals try nlinarith
  · -- Third part: ∀ t, iteratedDeriv 2 x t = -A * ω^2 * sin (ω * t)
    intro t 
    -- First establish what iteratedDeriv 2 x is
    have h4 : iteratedDeriv 2 x = deriv (deriv x) := by 
      simp [iteratedDeriv_succ]
      <;> aesop 
      <;> aesop 
      all_goals try nlinarith 
      all_goals try norm_num 
      all_goals try ring 
      all_goals try simp [mul_assoc]
      <;> try norm_num 
      <;> try tauto 
      all_goals try nlinarith 
      all_goals try tauto 
    -- Calculate the value at t 
    rw [h4]
    simp [eq2]
    all_goals try norm_num 
    all_goals try tauto 
    all_goals norm_num
    all_goals norm_num
    all_goals try tauto 
    all_goals norm_num
    all_goals try nlinarith 
    all_goals try tauto