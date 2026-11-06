import Mathlib

open Real

theorem number_theory_4531 {u : ℕ → ℕ} (hu0 : u 0 = 1) (hu1 : u 1 = 1)
    (hun :∀ n, u (n + 2) = u (n + 1) + u n) {α : ℝ} (hα : α = (1 + √5) / 2) (n : ℕ) :
    α ^ n < u (n + 2) := by

  have h2 : ∀ (n : ℕ), (u (n + 2) : ℝ) = (u (n + 1) : ℝ) + (u n : ℝ) := by
    intro n
    exact_mod_cast hun n

  have h3 : α ^ 2 = α + 1 := by
    rw [hα]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h4 : ∀ (n : ℕ), α ^ n < (u (n + 2) : ℝ) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num [hα, hu0, hu1, hun]
    | succ n =>
      cases n with
      | zero =>
        norm_num [hα, hu0, hu1, hun]
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      | succ n =>
        have h5 : α ^ (n) < (u (n + 2) : ℝ) := by
          apply ih n
          all_goals
            linarith
        have h6 : α ^ (n + 1) < (u (n + 3) : ℝ) := by
          apply ih (n + 1)
          all_goals
            linarith
        have h13 : α ^ (n + 2) = α ^ (n + 1) + α ^ (n) := by
          calc
            α ^ (n + 2) = α ^ n * (α ^ 2) := by ring
            _ = α ^ n * (α + 1) := by rw [h3]
            _ = α ^ (n + 1) + α ^ n := by ring
        have h14 : (u (n + 4) : ℝ) = (u (n + 3) : ℝ) + (u (n + 2) : ℝ) := by
          specialize h2 (n + 2)
          simpa using h2
        have h15 : α ^ (n + 1) < (u (n + 3) : ℝ) := by
          linarith [h6]
        have h16 : α ^ (n) < (u (n + 2) : ℝ) := by
          linarith [h5]
        have h17 : α ^ (n + 1) + α ^ (n) < (u (n + 3) : ℝ) + (u (n + 2) : ℝ) := by
          linarith
        have h18 : (α ^ (n + 2) : ℝ) = α ^ (n + 1) + α ^ (n) := by
          linarith [h13]
        have h19 : (α ^ (n + 2) : ℝ) < (u (n + 4) : ℝ) := by
          linarith [h14, h18, h17]
        simpa using h19

  have h4' : α ^ n < (u (n + 2) : ℝ) := by
    apply h4 n

  simpa using h4'