import Mathlib

theorem algebra_11419 {a : ℕ → ℤ} (ha1 : a 1 = 1) (han : ∀ n > 0, a (n + 1) = 2 * a n + 1) :
    ∀ n > 0, a n = 2 ^ n - 1 := by
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
      have ih' := ih (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega, h1, ih']
      <;> ring_nf
      <;> omega