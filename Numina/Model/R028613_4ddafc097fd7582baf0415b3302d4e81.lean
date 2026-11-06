import Mathlib

theorem algebra_88955 {f : ℕ → ℕ} (h1 : f 1 = 1) (h2 : ∀ n, 0 < n → f (2 * n) = n * f n) :
    f (2 ^ 100) = 2 ^ 4950 := by
  have h3 : ∀ (n : ℕ), f (2 ^ n) = 2 ^ (∑ i in Finset.range n, i) := by
    intro n 
    induction n with 
    | zero =>
      simp [h1]
    | succ n ih =>
      have h61 : f (2 ^ (n + 1)) = 2 ^ n * f (2 ^ n) := by 
        have h44 : f (2 * (2 ^ n)) = (2 ^ n) * f (2 ^ n) := h2 (2 ^ n) (by positivity)
        have h13 : 2 ^ (n + 1) = 2 * (2 ^ n) := by ring_nf
        rw [h13] at *
        exact h44
      have h62 : f (2 ^ n) = 2 ^ (∑ i in Finset.range n, i) := ih
      have h63 : ∑ i in Finset.range (n + 1), i = (∑ i in Finset.range n, i) + n := by 
        rw [Finset.sum_range_succ]
      rw [h61]
      have h7 : 2 ^ n * 2 ^ (∑ i in Finset.range n, i) = 2 ^ (∑ i in Finset.range (n + 1), i) := by
        rw [← pow_add]
        rw [h63]
        <;> ring_nf
      rw [h62]
      exact h7
  have h4 : f (2 ^ 100) = 2 ^ (∑ i in Finset.range 100, i) := h3 100
  rw [h4] 
  have h5 : ∑ i in Finset.range 100, i = 4950 := by
    norm_num [Finset.sum_range_succ]
  rw [h5]