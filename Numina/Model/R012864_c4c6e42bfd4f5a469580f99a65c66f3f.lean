import Mathlib

theorem algebra_134712 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n ≥ 1, (n ^ 2 * a n) = ∑ i in Finset.Icc 1 n, a i) :
    ∀ n ≥ 1, a n = 1 / (n * (n + 1)) := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h1 := han (n + 1) (by linarith)
      have h2 := han (n + 2) (by linarith)
      rw [ih (by linarith)] at h1
      simp [Finset.sum_Icc_succ_top, add_assoc] at h1 h2 ⊢
      field_simp at h1 h2 ⊢
      ring_nf at h1 h2 ⊢
      nlinarith