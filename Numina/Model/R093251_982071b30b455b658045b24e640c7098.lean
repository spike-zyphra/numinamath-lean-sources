import Mathlib

theorem algebra_197885 {f : ℤ → ℤ} (h0 : f 0 = 1) (h : ∀ x, f (x + 4) = f x + 3 * x + 4) :
    f 4000 = 5998001 := by 
  have h1 : ∀ (n : ℕ), f (4 * (n : ℤ)) = 1 + ∑ k in Finset.range n, (12 * (k : ℤ) + 4) := by 
    intro n 
    induction n with 
    | zero =>
      simp [h0]
    | succ n ih =>
      have eq1 : f (4 * ((n + 1 : ℕ) : ℤ)) = f (4 * ((n : ℕ) : ℤ) + 4) := by 
        simp [mul_add, mul_one]
        all_goals ring_nf 
        <;> try ring 
        <;> try omega 
      rw [eq1]
      rw [h]
      rw [ih]
      simp [Finset.sum_range_succ]
      <;> try ring 
      <;> try omega 
  have eq1 := h1 1000 
  norm_num [Finset.sum_range_succ] at eq1 ⊢
  <;> try linarith