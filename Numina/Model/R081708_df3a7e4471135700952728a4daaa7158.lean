import Mathlib

theorem algebra_184992 {a : ℕ → ℤ} (ha1 : a 1 = 1) (han : ∀ n ≥ 2, a n = 2 * a (n - 1) + n - 2) :
    ∀ n ≥ 1, a n = 2 ^ n - n := by
  intro n hn
  induction n with
  | zero => 
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      simp [ha1]
    | succ n => 
      have h := ih (by linarith)
      specialize han (n + 2) (by linarith)
      simp [show n + 2 = n + 2 by rfl, show (n + 2 - 1 : ℕ) = n + 1 by omega] at han
      simp [han, h, pow_succ, pow_zero]
      <;> ring_nf <;> omega