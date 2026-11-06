import Mathlib

theorem algebra_121691 {a b : ℕ → ℝ} (ha : ∀ i, a i ≠ 1)
    (hb : ∀ n, b n = 1 - a n) (n : ℕ) :
    ∑ i in Finset.Icc 1 n, a i * ∏ j in Finset.Icc 1 (i - 1), b j =
    1 - ∏ j in Finset.Icc 1 n, b j := by
  have h1 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, a i * ∏ j in Finset.Icc 1 (i - 1), b j =
      1 - ∏ j in Finset.Icc 1 n, b j := by 
    intro n 
    induction n with
    | zero => 
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [Finset.prod_Icc_succ_top (by linarith)]
      simp [hb] at ih ⊢ 
      <;> linarith [ih, ha k, ha (k + 1)]
  specialize h1 n
  simpa using h1