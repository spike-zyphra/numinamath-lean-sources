import Mathlib

theorem algebra_104333 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 + 2 * x) (n : ℕ) :
    ∀ x, f^[n] x = (x + 1) ^ (2 ^ n) - 1 := by 
  intro x
  have h1 : ∀ (n : ℕ), f^[n] x = (x + 1) ^ (2 ^ n) - 1 := by
    intro n 
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      have eq1 : f^[n + 1] x = f (f^[n] x) := by 
        simp [Function.iterate_succ_apply']
      rw [eq1]
      rw [ih]
      rw [hf]
      simp [pow_mul, pow_add, mul_add]
      <;> ring
  specialize h1 n 
  simpa using h1