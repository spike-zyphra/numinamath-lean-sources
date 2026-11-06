import Mathlib
open Real
theorem algebra_599145 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2) (han : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, a i = n ^ 2 * a n) :
∀ n, n ≥ 1 → a n = 1 / (n * (n + 1)):= by
  intro n hn
  have h1 : ∀ (n : ℕ), n ≥ 1 → a n = 1 / ((n : ℝ) * ((n + 1 : ℝ))) := by
    intro n hn
    induction n with
    | zero => linarith
    | succ n ih =>
      cases n with
      | zero =>
        rw [ha1]
        norm_num
      | succ n => 
        have eq1 := han (n + 1) (by linarith)
        have eq2 := han (n + 2) (by linarith)
        simp [Finset.sum_Icc_succ_top, mul_add, add_mul] at eq1 eq2
        simp [ih (by linarith)] at eq1 eq2
        field_simp at eq1 eq2 ⊢
        ring_nf at eq1 eq2 ⊢
        <;> nlinarith [sq_nonneg (a (n + 1) : ℝ), sq_nonneg (a (n + 2) : ℝ)]
  specialize h1 n hn
  simpa using h1