import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_189417 {a : ℝ} (ha : a = π / 2 - 1) :
    ∀ b : ℝ, ∃ x ∈ Icc (-1) 1, |x| - arcsin x + b * (arccos x + abs x - 1) + π / 2 - 1 = 0 := by
  intro b
  use 1
  constructor
  · -- Show that 1 is in the interval [-1, 1]
    exact ⟨by norm_num, by norm_num⟩
  · -- Show that the equation is satisfied at x = 1 with a = π / 2 - 1
    have h1 : |(1 : ℝ)| = 1 := by
      norm_num [abs_one]
    have h2 : arcsin (1 : ℝ) = π / 2 := Real.arcsin_one
    have h3 : arccos (1 : ℝ) = 0 := by 
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      rw [h2]
      linarith [Real.pi_pos]
    rw [h1, h2, h3]
    all_goals
      ring_nf
      <;> norm_num
      all_goals
        linarith [Real.pi_pos]