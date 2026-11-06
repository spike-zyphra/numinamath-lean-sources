import Mathlib

open Finset

theorem algebra_311731 {S : Finset ℝ} (hS : S = {0, 10}) :
    ∀ x : ℝ, ∃ p : Polynomial ℝ, p.degree ≥ 1 ∧ ∀ i ∈ range (p.natDegree + 1), p.coeff i ∈ S ∧
      p.eval x = 0 → x ∈ S := by
  intro x 
  use Polynomial.C (10 : ℝ) * Polynomial.X
  constructor
  · -- Show that the degree of polynomial is ≥ 1
    rw [Polynomial.degree_mul]
    all_goals -- apply to goal
      simp [Polynomial.degree_C, Polynomial.degree_X, show (10 : ℝ) ≠ 0 by norm_num]
  · -- Show that if i ∈ range (natDegree +1), p.coeff i ∈ S ∧ p.eval x =0 → x ∈ S
    intro i hi h1
    rw [hS]
    have hx : x = 0 := by
      have eqn : (Polynomial.C (10 : ℝ) * Polynomial.X).eval x = 0 := by 
        simpa using h1.2
      simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at eqn ⊢
      <;> nlinarith 
    simp [hx, Finset.mem_insert, Finset.mem_singleton]