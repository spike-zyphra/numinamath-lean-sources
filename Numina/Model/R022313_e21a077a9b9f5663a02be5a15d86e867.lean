import Mathlib

theorem algebra_306165 {a : ℕ → ℤ} (ha1 : a 1 = 3)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * n + 3) :
    ∀ n ≥ 1, a n = n * (n + 2) := by
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
      have h2 := han (n + 1) (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega] at h2
      simp [h1] at h2
      simp [h2]
      <;> ring