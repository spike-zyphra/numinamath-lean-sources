import Mathlib

theorem algebra_227025 {n : ℕ} {A B a d : ℤ} (hA : A = ∑ i in Finset.range n, (i * d + a)) (hB : B = ∑ i in Finset.range (2 * n), (i * d + a)) :
    ∑ i in Finset.range (3 * n), (i * d + a) = 3 * (B - A) := by 
  have h1 : ∀ n : ℕ, ∑ i in Finset.range (3 * n), (i * d + a) = 3 * (∑ i in Finset.range (2 * n), (i * d + a) - ∑ i in Finset.range n, (i * d + a)) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show 3 * (n + 1) = 3 * n + 3 by ring]
      rw [show 2 * (n + 1) = 2 * n + 2 by ring]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp [Finset.sum_range_succ, mul_add, mul_assoc]
      all_goals
        ring
  specialize h1 n
  rw [h1, hA, hB]