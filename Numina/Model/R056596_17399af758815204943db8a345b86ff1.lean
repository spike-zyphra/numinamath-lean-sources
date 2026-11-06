import Mathlib

theorem algebra_98281 (a : ℕ → ℝ) (ha : a 0 = 5) (h : ∀ n, a (n + 1) = a n + 7)
    (h' : ∑ i in Finset.range 30, a i = x) :
    x = 3195 := by 
  have eqn : ∀ n, a n = 5 + 7 * (n : ℝ) := by 
    intro n 
    induction n with 
    | zero =>
      simp [ha]
    | succ n ih =>
      simp [h, ih]
      <;> ring
  have h_eq : x = ∑ i in Finset.range 30, a i := by rw [← h']
  rw [h_eq]
  simp_rw [eqn]
  norm_num [Finset.sum_range_succ]
  <;> ring_nf