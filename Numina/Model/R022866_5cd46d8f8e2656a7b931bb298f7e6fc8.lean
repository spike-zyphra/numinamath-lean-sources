import Mathlib

theorem algebra_12406 {a : ℕ → ℝ} (ha1 : a 1 = 0) (han : ∀ n > 0, a (n + 1) = ((n + 2) / n) * a n + (1 / n)) :
    ∀ n > 0, a n = ((n - 1) * (n + 2)) / 4 := by
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
      have h1 := ih (by linarith)
      have h2 := han (n + 1) (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega] at h2 ⊢
      rw [h2]
      rw [h1]
      field_simp
      ring