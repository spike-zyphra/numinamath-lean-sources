import Mathlib

theorem algebra_109851 (n : ℕ) :
    ∑ k in Finset.Icc 1 n, k = n * (n + 1) / 2 ∧
    ∑ k in Finset.Icc 1 n, k^2 = n * (n + 1) * (2 * n + 1) / 6 := by 
  constructor
  · -- First part: prove the sum of the first n natural numbers equals n(n+1)/2
    induction n with
    | zero =>
      simp [Finset.sum_eq_zero]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih]
      ring_nf
      <;> omega
  · -- Second part: prove the sum of the squares of the first n natural numbers equals n(n+1)(2n+1)/6
    induction n with
    | zero =>
      simp [Finset.sum_eq_zero]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih]
      simp [add_assoc]
      <;> ring_nf <;> omega