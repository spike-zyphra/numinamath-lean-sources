import Mathlib

theorem algebra_112646 {u : ℕ → ℝ} (hu1 : u 1 = 1 / 2)
    (hsum : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, u i = n ^ 2 * u n) :
    ∀ n ≥ 1, u n = 1 / (n * (n + 1)) := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [show (1 : ℕ) = 1 by rfl]
      rw [hu1]
      norm_num
    | succ n =>
      have eq1 := hsum (n + 1) (by linarith)
      have eq2 := hsum (n + 2) (by linarith)
      simp [Finset.sum_Icc_succ_top, mul_add, add_mul] at eq1 eq2
      have h2 := ih (by linarith)
      field_simp at eq1 eq2 h2 ⊢
      ring_nf at eq1 eq2 h2 ⊢
      nlinarith [h2, eq1, eq2]