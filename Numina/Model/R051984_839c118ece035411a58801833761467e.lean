import Mathlib

theorem algebra_171585 (f : ℝ → ℝ) (h : ∀ x, f (x + 1) = f x + 2 * x + 3) (h0 : f 0 = 1) :
    f 2012 = 2013 ^ 2 := by
  have eqn (n : ℕ) : f (n : ℝ) = ((n : ℝ) + 1) ^ 2 := by
    induction n with
    | zero =>
      specialize h0
      norm_num at h0 ⊢
      linarith
    | succ n ih =>
      have eq1 := h (n : ℝ)
      norm_num at eq1 ⊢ 
      rw [eq1]
      rw [ih]
      ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
  specialize eqn 2012
  norm_num at eqn ⊢
  linarith