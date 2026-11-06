import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_174712 {u : ℝ → ℝ → ℝ}
  (hu : ∀ x t, u x t = 3 / 4 * exp (-4 * π ^ 2 * t) * sin (2 * π * x) -
    1 / 4 * exp (-36 * π ^ 2 * t) * sin (6 * π * x)) :
  (∀ x t, u x t = 3 / 4 * exp (-4 * π ^ 2 * t) * sin (2 * π * x) -
    1 / 4 * exp (-36 * π ^ 2 * t) * sin (6 * π * x)) ∧
  (∀ x, u x 0 = sin (2 * π * x) ^ 3) ∧
  (∀ t, u 0 t = 0 ∧ u 1 t = 0) := by

  constructor
  · -- Show that the formula of $u$ is as claimed.
    intro x t
    exact_mod_cast (hu x t)
  constructor
  · -- Show that $u(x, 0) = \sin (2 * \pi * x) ^ 3$ for all $x$.
    intro x
    have eq1 : u x 0 = 3 / 4 * exp (-4 * π ^ 2 * (0 : ℝ)) * sin (2 * π * x) - 1 / 4 * exp (-36 * π ^ 2 * (0 : ℝ)) * sin (6 * π * x) := by
      specialize hu x 0
      simpa using hu
    rw [eq1]
    have hexp1 : exp (-4 * π ^ 2 * (0 : ℝ)) = 1 := by
      norm_num
    have hexp2 : exp (-36 * π ^ 2 * (0 : ℝ)) = 1 := by
      norm_num
    rw [hexp1, hexp2]
    have h1 : sin (6 * π * x) = 3 * sin (2 * π * x) - 4 * sin (2 * π * x) ^ 3 := by
      have h2 : sin (6 * π * x) = sin (3 * (2 * π * x)) := by ring_nf
      rw [h2]
      rw [sin_three_mul]
      <;> ring_nf
    rw [h1]
    have : (3 / 4 : ℝ) * sin (2 * π * x) - (1 / 4 : ℝ) * (3 * sin (2 * π * x) - 4 * sin (2 * π * x) ^ 3) = sin (2 * π * x) ^ 3 := by
      ring_nf
    linarith
  · -- Show that for all $t$, $u(0, t) = 0$ and $u(1, t) = 0$.
    intro t
    have h1 : u 0 t = 0 := by
      rw [hu 0 t]
      have h2 : sin (2 * π * (0 : ℝ)) = 0 := by
        simp
      have h3 : sin (6 * π * (0 : ℝ)) = 0 := by
        simp
      rw [h2, h3]
      all_goals norm_num
    have h4 : u 1 t = 0 := by
      rw [hu 1 t]
      have h2 : sin (2 * π * (1 : ℝ)) = 0 := by
        have : 2 * π * (1 : ℝ) = 2 * π := by ring
        rw [this]
        have : sin (2 * π) = 0 := Real.sin_two_pi
        exact_mod_cast this
      have h3 : sin (6 * π * (1 : ℝ)) = 0 := by
        have : 6 * π * (1 : ℝ) = 6 * π := by ring
        rw [this]
        have h4sin : sin (6 * π) = 0 := by
          have h : 6 * π = 3 * (2 * π) := by ring_nf
          rw [h]
          have h5 : sin (3 * (2 * π)) = 0 := by
            have h7 : sin (3 * (2 * π)) = 3 * sin (2 * π) - 4 * sin (2 * π) ^ 3 := by
              rw [sin_three_mul]
            rw [h7]
            have h8 : sin (2 * π) = 0 := Real.sin_two_pi
            rw [h8]
            all_goals norm_num
          linarith [h5]
        exact_mod_cast h4sin
      rw [h2, h3]
      all_goals norm_num
    exact ⟨h1, h4⟩