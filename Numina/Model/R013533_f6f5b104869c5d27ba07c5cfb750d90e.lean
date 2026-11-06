import Mathlib

open MvPolynomial

theorem algebra_18 {n : ℕ} {P : MvPolynomial (Fin n) ℝ} :
    ∃ Q R : MvPolynomial (Fin n) ℝ,
      P = Q - R ∧ ∀ x : Fin n → ℝ,
        MvPolynomial.eval x Q ≥ 0 ∧ MvPolynomial.eval x R ≥ 0 := by 
  use P ^ 2 + 1 
  use P ^ 2 + 1 - P 
  constructor
  · -- Show P = Q - R 
    ring_nf 
  · -- Show ∀ x : Fin n → ℝ, MvPolynomial.eval x Q ≥ 0 ∧ MvPolynomial.eval x R ≥ 0 
    intro x 
    have h1 : MvPolynomial.eval x (P ^ 2 + 1) ≥ 0 := by
      have eq1 : MvPolynomial.eval x (P ^ 2 + 1) = (MvPolynomial.eval x P) ^ 2 + (1 : ℝ) := by 
        simp [pow_two, MvPolynomial.eval_add, MvPolynomial.eval_pow]
      rw [eq1] 
      have h3 : (MvPolynomial.eval x P) ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      linarith 
    have h2 : MvPolynomial.eval x (P ^ 2 + 1 - P) ≥ 0 := by 
      have eq2 : MvPolynomial.eval x (P ^ 2 + 1 - P) = (MvPolynomial.eval x (P ^ 2 + 1)) - (MvPolynomial.eval x P) := by 
        simp [MvPolynomial.eval_sub] 
      rw [eq2] 
      have eq1' : MvPolynomial.eval x (P ^ 2 + 1) = (MvPolynomial.eval x P) ^ 2 + (1 : ℝ) := by 
        simp [pow_two, MvPolynomial.eval_add, MvPolynomial.eval_pow]
      rw [eq1']
      have h4 : (MvPolynomial.eval x P) ^ 2 + (1 : ℝ) - (MvPolynomial.eval x P) ≥ 0 := by 
        nlinarith [sq_nonneg ((MvPolynomial.eval x P) - (1 / 2 : ℝ))]
      linarith 
    constructor 
    · -- Show MvPolynomial.eval x Q ≥ 0 
      linarith [h1] 
    · -- Show MvPolynomial.eval x R ≥ 0 
      linarith [h2]