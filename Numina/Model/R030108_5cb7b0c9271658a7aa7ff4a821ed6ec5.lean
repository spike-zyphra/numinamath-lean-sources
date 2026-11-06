import Mathlib


theorem algebra_326141 {x : ℕ → ℝ} (hx1 : x 1 = 3)
    (hxn : ∀ n ≥ 1, x (n + 1) = (2 / (n ^ 2) + 3 / n + 1) * x n + n + 1) :
    ∀ n ≥ 1, x n = n ^ 2 * (2 * n + 1) := by 
  intro n hn
  induction n with
  | zero => 
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [hx1]
      norm_num
    | succ n =>
      have h2 := ih (by linarith)
      have eq1 := hxn (n + 1) (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega] at eq1 ⊢
      rw [eq1]
      rw [h2]
      field_simp
      ring