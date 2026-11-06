import Mathlib

theorem algebra_13990 {a : ℕ → ℝ} (ha1 : a 1 = 1) (han : ∀ n > 0, a (2 * n) = n * a n) :
    a (2 ^ 100) = 2 ^ 4950 := by
  have h : ∀ k : ℕ, a (2 ^ k) = 2 ^ (∑ i in Finset.range k, (i : ℕ)) := by
    intro k
    induction k with
    | zero =>
      simp [ha1]
      <;> norm_num
    | succ k ih =>
      have h1 : a (2 ^ (k + 1)) = (2 ^ k : ℝ) * a (2 ^ k) := by
        have h2 : (2 ^ (k + 1 : ℕ)) = 2 * (2 ^ k) := by ring
        rw [h2]
        have h4 : a (2 * (2 ^ k)) = (2 ^ k : ℝ) * a (2 ^ k) := by
          specialize han (2 ^ k) (by positivity)
          norm_num at han ⊢
          linarith
        exact h4
      rw [h1]
      rw [ih]
      simp [Finset.sum_range_succ]
      <;> ring_nf <;> norm_num
  specialize h 100
  norm_num [Finset.sum_range_succ] at h ⊢
  <;> linarith