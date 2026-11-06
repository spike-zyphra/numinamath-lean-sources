import Mathlib

theorem algebra_148894 {a x y : ℕ → ℝ}
  (hx0 : x 0 = 1) (hy0 : y 0 = 0)
  (hx : ∀ n, x n.succ = x n - y n)
  (hy : ∀ n, y n.succ = x n + y n)
  (ha : ∀ n, a n = (x n.succ - x n) * (x (n + 2) - x n.succ) + (y n.succ - y n) * (y (n + 2) - y n.succ)) :
  IsLeast {n | ∑ i ∈ Finset.range n, a i > 1000} 10 := by
  have ha1 : ∀ (n : ℕ), a n = 2 ^ n := by
    intro n 
    induction' n with n ih
    · norm_num [ha, hx0, hy0, hx, hy]
    · have h1 : a n = 2 ^ n := ih
      have h2 : a (n + 1) = 2 * a n := by
        simp [ha, hx, hy] at * 
        <;> ring_nf
        <;> linarith [ih]
      rw [h2]
      rw [h1]
      ring_nf
  constructor
  · -- Show that 10 is in the set
    show ∑ i in Finset.range 10, a i > 1000
    norm_num [Finset.sum_range_succ, ha1]
    <;> norm_num 
    <;> linarith 
  · -- Show that 10 is the smallest
    intro n hn
    have h1 : ∑ i in Finset.range n, a i > 1000 := by 
      simpa using hn 
    by_contra h
    push_neg at h 
    have h2 : ∑ i in Finset.range n, a i ≤ 1000 := by
      interval_cases n <;> norm_num [Finset.sum_range_succ, ha1] at *
    linarith