import Mathlib

theorem algebra_299957 {a : ℕ → ℤ} (ha1 : a 1 = 1) (han : ∀ n ≥ 2, a n = 2 * a (n - 1) + n - 2) :
    ∀ n, n ≥ 1 → a n = 2 ^ n - n := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      simp [ha1]
    | succ n => 
      have h := han (n + 2) (by omega)
      simp [show n + 2 = (n + 1) + 1 by omega] at h
      simp [h, ih]
      <;> ring_nf
      <;> omega