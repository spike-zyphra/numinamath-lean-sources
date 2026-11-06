import Mathlib

theorem algebra_602205 {n : ℕ} (hn : 0 < n) (x y : ℕ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, c k = ∑ i in Finset.Icc 1 k, y i) :
    ∑ i in Finset.Icc 1 n, x i * y i =
    ∑ i in Finset.Icc 1 (n - 1), (x i - x (i + 1)) * c i +
    x n * c n := by
  induction n with
  | zero =>
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      simp [hc, Finset.sum_Icc_succ_top, mul_add, add_mul] at ih ⊢
      <;> linarith
    | succ n =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih (by linarith)]
      simp [hc, Finset.sum_Icc_succ_top, mul_add, add_mul]
      <;> linarith