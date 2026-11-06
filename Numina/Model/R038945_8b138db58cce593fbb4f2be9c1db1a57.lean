import Mathlib

open Real

theorem algebra_319809 {a : ℕ → ℝ} (ha1 : a 1 = 1) (han : ∀ n, a (n + 1) = a n + sqrt (a n) + 1 / 4) :
    a 99 = 2500 := by

  have h1 : ∀ n : ℕ, a (n + 1) = ((↑n + 2) / 2) ^ 2 := by

    intro n
    induction n with
    | zero =>
      norm_num [ha1]

    | succ n ih =>
      rw [show a (n + 1 + 1) = a (n + 1) + sqrt (a (n + 1)) + 1 / 4 by simpa using han (n + 1)]
      rw [ih]
      have h2 : sqrt (((↑n + 2) / 2) ^ 2) = (↑n + 2) / 2 := by
        rw [Real.sqrt_sq (by positivity)]

      rw [h2]
      field_simp
      ring
  specialize h1 98
  norm_num at h1 ⊢
  all_goals linarith