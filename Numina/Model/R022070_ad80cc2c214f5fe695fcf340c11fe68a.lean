import Mathlib

theorem algebra_10911 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * n) :
    ∀ n ≥ 1, a n = n ^ 2 - n + 2 := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      norm_num [ha1]
    | succ n =>
      have h1 := ih (by linarith)
      have eq2 := han (n + 1) (by linarith)
      simp [eq2] at *
      simp [h1] at *
      ring_nf at *
      <;> linarith