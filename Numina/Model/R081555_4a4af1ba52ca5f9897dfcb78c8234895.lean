import Mathlib

theorem algebra_10135 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n > 0, a (n + 1) = 1 / 2 * a n + (2 * n + 3) / 2 ^ (n + 1)) :
    ∀ n > 0, a n = (n ^ 2 + 2 * n - 2) / 2 ^ n := by 
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
      have h1 := ih (by linarith)
      have h2 := han (n+1) (by linarith)
      simp [show n + 1 ≥ 1 by linarith] at h2
      simp [h2, h1]
      all_goals field_simp
      all_goals ring