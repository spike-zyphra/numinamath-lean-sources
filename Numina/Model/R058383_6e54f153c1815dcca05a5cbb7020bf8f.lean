import Mathlib

theorem algebra_306183 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 3 + (1 / 2) * a n) :
    ∀ n ≥ 1, a n = 6 - (5 / 2 ^ (n - 1)) := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      simp [ha1]
      all_goals norm_num
    | succ n =>
      simp [show n + 1 ≥ 1 by omega] at han
      have h1 := han (n + 1) (show n + 1 ≥ 1 by omega)
      simp [h1]
      simp [ih (show n + 1 ≥ 1 by omega)]
      field_simp
      ring