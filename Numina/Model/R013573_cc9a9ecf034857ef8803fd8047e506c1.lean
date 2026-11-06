import Mathlib

theorem algebra_214014 {a : ℕ → ℤ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 3 * a n - 2 * n ^ 2 + 4 * n + 4) :
    ∀ n ≥ 1, a n = 3 ^ n + n ^ 2 - n - 2 := by
  intro n hn
  induction n with
  | zero =>
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have ih' := ih (by linarith)
      have h2 := han (n + 1) (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega] at h2
      simp [h2, ih']
      <;> ring_nf
      <;> omega