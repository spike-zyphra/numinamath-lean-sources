import Mathlib

theorem number_theory_188180 (x y : ℕ → ℤ) (hx1 : x 1 = 2) (hy1 : y 1 = 1)
    (hxn : ∀ k ≥ 2, x k = 2 * x (k - 1) + 3 * y (k - 1))
    (hy : ∀ k ≥ 2, y k = x (k - 1) + 2 * y (k - 1)) :
    ∃ c, ∀ k ≥ 1, x k ^ 2 - 3 * y k ^ 2 = c := by
  use 1
  intro k hk
  induction k with
  | zero =>
    exfalso
    linarith
  | succ k ih =>
    cases k with
    | zero =>
      norm_num [hx1, hy1]
    | succ k =>
      have h2 : x (k + 1 + 1) = 2 * x (k + 1) + 3 * y (k + 1) := by
        specialize hxn (k + 1 + 1) (by linarith)
        simpa using hxn
      have h3 : y (k + 1 + 1) = x (k + 1) + 2 * y (k + 1) := by 
        specialize hy (k + 1 + 1) (by linarith)
        simpa using hy
      rw [show k + 1 + 1 = k + 2 by omega] at *
      specialize ih (by linarith)
      rw [h2, h3]
      nlinarith [ih]