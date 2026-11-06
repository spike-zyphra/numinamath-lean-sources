import Mathlib

theorem algebra_252477 {n : ℕ} (hn : 0 < n) (a b : ℕ → ℝ) :
    ∑ i in Finset.Icc 1 n, a i * b i =
    ∑ i in Finset.Icc 1 (n - 1), (a i - a (i + 1)) * ∑ j in Finset.Icc 1 i, b j +
    a n * ∑ i in Finset.Icc 1 n, b i := by
  have h1 : ∀ n : ℕ, 0 < n → ∑ i in Finset.Icc 1 n, a i * b i =
      ∑ i in Finset.Icc 1 (n - 1), (a i - a (i + 1)) * ∑ j in Finset.Icc 1 i, b j +
      a n * ∑ i in Finset.Icc 1 n, b i := by
    intro n hn
    induction n with
    | zero => 
      simp at hn
    | succ n ih =>
      cases n with
      | zero => 
        simp 
      | succ n =>
        simp [Finset.sum_Icc_succ_top, mul_add, add_mul, mul_comm, mul_assoc] at ih ⊢
        <;> linarith 
  specialize h1 n hn
  simpa using h1