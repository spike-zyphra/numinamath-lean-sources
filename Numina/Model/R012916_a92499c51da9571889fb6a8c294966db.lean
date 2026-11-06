import Mathlib

theorem algebra_327122 {a b : ℕ → ℝ} {A B : ℕ → ℝ}
    (ha : ∀ n, A n = ∑ i in Finset.Icc 1 n, a i)
    (hb : ∀ n, B n = ∑ i in Finset.Icc 1 n, b i)
    (c : ℕ → ℝ) (hc : ∀ n, c n = a n * B n + b n * A n - a n * b n) :
    ∑ i in Finset.Icc 1 10, c i = A 10 * B 10 := by
  norm_num [Finset.sum_Icc_succ_top, hc, ha, hb]
  <;> ring_nf
  <;> simp [Finset.sum_Icc_succ_top, ha, hb, hc]
  <;> ring