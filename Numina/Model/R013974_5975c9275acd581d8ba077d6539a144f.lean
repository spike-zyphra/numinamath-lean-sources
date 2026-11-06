import Mathlib

open scoped BigOperators

theorem algebra_154962
  (a : ℕ → ℝ)
  (h₀ : a 0 = 6 / 7)
  (h₁ : ∀ n, a (n + 1) = if a n < 1 / 2 then 2 * a n else 2 * a n - 1) :
  a 2008 = 5 / 7 := by
  have h2 : ∀ (k : ℕ), a (3 * k + 1) = 5 / 7 := by
    intro k
    induction k with
    | zero =>
      norm_num [h₁, h₀]
    | succ k ih =>
      have eq1 : a (3 * (k + 1) + 1) = a (3 * k + 4) := by ring_nf
      rw [eq1] at *
      have h3 : a (3 * k + 2) = 3 / 7 := by
        have eq2 : a (3 * k + 2) = if a (3 * k + 1) < 1 / 2 then 2 * a (3 * k + 1) else 2 * a (3 * k + 1) - 1 := by
          specialize h₁ (3 * k + 1)
          simpa using h₁
        rw [eq2]
        rw [ih]
        norm_num [if_neg]
      have h4 : a (3 * k + 3) = 6 / 7 := by
        have eq2 : a (3 * k + 3) = if a (3 * k + 2) < 1 / 2 then 2 * a (3 * k + 2) else 2 * a (3 * k + 2) - 1 := by
          specialize h₁ (3 * k + 2)
          simpa using h₁
        rw [eq2]
        rw [h3]
        norm_num [if_pos]
      have h5 : a (3 * k + 4) = 5 / 7 := by
        have eq2 : a (3 * k + 4) = if a (3 * k + 3) < 1 / 2 then 2 * a (3 * k + 3) else 2 * a (3 * k + 3) - 1 := by
          specialize h₁ (3 * k + 3)
          simpa using h₁
        rw [eq2]
        rw [h4]
        norm_num [if_neg]
      all_goals linarith
  have h3 : 2008 = 3 * 669 + 1 := by norm_num
  rw [h3]
  apply h2