import Mathlib
set_option exponentiation.threshold 5000
theorem algebra_95206  {f : ℕ → ℕ}
(h1 : f 1 = 1) (h2 : ∀ n > 0, f (2 * n) = n * f n) : f (2 ^ 100) = 2 ^ 4950 := by
  have mainth : ∀ (n : ℕ), f (2 ^ n) = 2 ^ (∑ i in Finset.range n, i) := by
    intro n
    induction n with
    | zero =>
      simp [h1]
    | succ n ih =>
      have h3 : f (2 ^ (n + 1)) = f (2 * 2 ^ n) := by
        ring_nf
      have h4 : f (2 * 2 ^ n) = 2 ^ n * f (2 ^ n) := by
        specialize h2 (2 ^ n) (by positivity)
        simpa using h2
      rw [h3, h4, ih]
      simp [Finset.sum_range_succ]
      <;> ring_nf
  have h4 : f (2 ^ 100) = 2 ^ (∑ i in Finset.range 100, i) := by
    apply mainth
  rw [h4]
  native_decide