import Mathlib

theorem algebra_119891 {a : ℕ → ℝ} (ha1 : a 1 = 3) (han : ∀ n > 0, n * a n = (n + 1) * a (n + 1)) :
    ∀ n > 0, a n = 3 / n := by 
  intro n hn
  induction n with
  | zero => linarith
  | succ n ih =>
    cases n with
    | zero =>
      simp [ha1]
    | succ n =>
      simp at ih ⊢
      have h1 := han (n + 1) (by linarith)
      have h2 := han (n + 2) (by linarith)
      simp [ih] at h1
      field_simp at h1 ⊢
      linarith