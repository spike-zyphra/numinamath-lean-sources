import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_210531 {A : ℝ} (hA : ∀ f : ℝ → ℝ, (∃ a b c, f = λ x => a*x^2 + b*x + c) ∧
    ∀ x ∈ Icc 0 1, |f x| ≤ 1 → |deriv f 0| ≤ A) :
    A ≥ 8 := by 
  by_contra h
  push_neg at h
  
  have h1 := hA (fun x => -8 * x^2 + 8 * x - 1)
  have h2 : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) 1 → 
    |(fun x => -8 * x^2 + 8 * x - 1) x| ≤ 1 → |deriv (fun x => -8 * x^2 + 8 * x - 1) 0| ≤ A := by 
    have h1' := h1.2 
    simpa using h1'
  
  -- Show that for x = 0, |f(x)| ≤ 1
  have h4 : |(fun x => -8 * x^2 + 8 * x - 1) (0 : ℝ)| ≤ 1 := by 
    norm_num [abs_le]
    all_goals norm_num
  
  have h5 : |(fun x => -8 * x^2 + 8 * x - 1) (0 : ℝ)| ≤ 1 := by 
    have h6 : |(fun x => -8 * x^2 + 8 * x - 1) (0 : ℝ)| ≤ 1 := by 
      norm_num [abs_le]
      all_goals norm_num
    linarith [h6]

  have h3 := h2 0 (by norm_num) h5
  
  have h7 : deriv (fun x => -8 * x^2 + 8 * x - 1) 0 = (8 : ℝ) := by 
    simp [deriv_const, deriv_pow, deriv_add, deriv_sub, deriv_id', mul_comm]
    all_goals norm_num 
    all_goals field_simp [deriv_pow, deriv_const, deriv_add, deriv_sub, mul_comm]
    all_goals norm_num [deriv_pow, deriv_const, deriv_add, deriv_sub, mul_comm]
    all_goals norm_num 
    all_goals try { tauto }
  
  have h8 : |deriv (fun x => -8 * x^2 + 8 * x - 1) 0| = (8 : ℝ) := by 
    rw [show deriv (fun x => -8 * x^2 + 8 * x - 1) 0 = (8 : ℝ) by linarith [h7]]
    all_goals norm_num [abs_of_pos]
    all_goals try { tauto }
  
  linarith [h3, h7, h8, h]