import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_136616 {y : ℝ → ℝ} (hy : y = λ x => sin (2 * x) + cos (x + 1)) (n : ℕ) :
    iteratedDeriv n y = λ x => 2 ^ n * sin (π / 2 * n + 2 * x) +
      cos (π / 2 * n + x + 1) := by 
  rw [hy]
  have eqn : ∀ (n : ℕ), 
    iteratedDeriv n (λ (x : ℝ) => sin (2 * x) + cos (x + 1)) 
      = λ x => 2 ^ n * sin (π / 2 * n + 2 * x) + cos (π / 2 * n + x + 1)
  := by 
    intro n 
    induction n with 
    | zero => 
      funext x 
      simp 
      <;> ring_nf <;> simp [sin_add, cos_add]
      <;> ring_nf <;> norm_num
      <;> try { tauto }
    | succ n ih => 
      have h1 : iteratedDeriv (n + 1) (λ (x : ℝ) => sin (2 * x) + cos (x + 1))
          = deriv (iteratedDeriv n (λ (x : ℝ) => sin (2 * x) + cos (x + 1))) := by 
          simp [iteratedDeriv_succ]
      rw [h1]
      rw [ih]
      funext x
      simp [deriv_add, deriv_mul, deriv_id'', mul_comm, mul_assoc, mul_add, add_mul, sin_add, cos_add, mul_assoc]
      <;> ring_nf <;> simp [sin_add, cos_add, mul_comm, mul_assoc, mul_add, add_mul, sin_add, cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two, mul_add, add_mul]
      <;> ring_nf <;> norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]
      <;> ring_nf <;> norm_num
      <;> try { tauto }
      <;> ring_nf <;> norm_num
      <;> try { ring }
      <;> try { norm_num }
      <;> try { ring_nf <;> norm_num }
  apply eqn n
  <;> try { tauto }