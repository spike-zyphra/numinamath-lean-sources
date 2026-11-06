import Mathlib

theorem algebra_165380 {a d : ℝ} (n : ℕ) :
    ∑ i in Finset.range (2 * n), (a + d * i) = ∑ i in Finset.range n, (a + d * i) +
    (1 / 3) * ∑ i in Finset.range (3 * n), (a + d * i) := by
  have h1 : ∀ n : ℕ, ∑ i in Finset.range (2 * n), (a + d * i) = ∑ i in Finset.range n, (a + d * i) + (1 / 3) * ∑ i in Finset.range (3 * n), (a + d * i) := by 
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by ring]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [show 3 * (n + 1) = 3 * n + 3 by ring]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      simp [Finset.sum_range_succ] at ih ⊢
      linarith 
  specialize h1 n
  simpa using h1