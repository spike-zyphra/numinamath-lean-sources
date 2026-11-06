import Mathlib

theorem algebra_301660 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 2, a n = 2^(2*n) * a (n - 1) + 2^(n^2) * n) :
    ∀ n ≥ 1, a n = 2^(n^2) * (2^(n + 1) - n - 2) := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h1 := ih (by linarith)
      have eq1 := han (n + 2) (by linarith)
      simp [show n + 2 = (n + 1) + 1 by omega] at eq1 ⊢
      simp [h1] at eq1 ⊢
      <;> ring_nf at eq1 ⊢
      <;> norm_num at eq1 ⊢
      <;> linarith