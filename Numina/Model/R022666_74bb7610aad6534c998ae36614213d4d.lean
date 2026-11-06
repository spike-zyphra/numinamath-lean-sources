import Mathlib

open Matrix

theorem calculus_16181 {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : ∀ a b c d : ℝ,
    M * !![a, b; c, d] = !![a, b; 3 * c, 3 * d]) :
    M = !![1, 0; 0, 3] := by
  have eq1 := hM 1 0 0 1
  have eqM00 : M 0 0 = 1 := by
    have h0 := congr_arg (λ m => m 0 0) eq1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, mul_one] at h0
    exact h0
  have eqM01 : M 0 1 = 0 := by
    have h1 := congr_arg (λ m => m 0 1) eq1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, mul_one] at h1
    exact h1
  have eqM10 : M 1 0 = 0 := by
    have h2 := congr_arg (λ m => m 1 0) eq1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, mul_one] at h2
    exact h2
  have eqM11 : M 1 1 = 3 := by
    have h3 := congr_arg (λ m => m 1 1) eq1
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, mul_one] at h3
    exact h3
  funext i j 
  fin_cases i <;> fin_cases j <;> simp [eqM00, eqM01, eqM10, eqM11] 
  <;> try { tauto }