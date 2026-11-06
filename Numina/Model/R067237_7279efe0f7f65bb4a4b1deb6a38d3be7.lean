import Mathlib

theorem algebra_292424 :
    ∃ a b c d : Fin 2007 → ℝ,
      (∑ i, a i * b i) = 2 * ∑ i, c i * d i := by 
  use (λ _ => (0 : ℝ)), (λ _ => (0 : ℝ)), (λ _ => (0 : ℝ)), (λ _ => (0 : ℝ))
  simp