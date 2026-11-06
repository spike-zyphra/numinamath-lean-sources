import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_14964 (k : ℝ) :
  (∃ t u, ∃ x y z, x = 2 + t * 1 ∧ y = 3 + t * 1 ∧ z = 4 + t * (-k) ∧
    x = 1 + u * k ∧ y = 4 + u * 2 ∧ z = 5 + u * 1) ↔ k = 0 ∨ k = -3 := by
  constructor
  · -- Assume the existence of t, u and x y z.
    rintro ⟨t, u, ⟨x, y, z, hx1, hy1, hz1, hx2, hy2, hz2⟩⟩
    have eq1 : t = 1 + 2 * u := by
      nlinarith
    -- Substituting into the first and second equations.
    -- From the first equation.
    have eq2 : 2 + t = 1 + u * k := by
      nlinarith [hx1, hx2]
    have eq3 : k * u = 2 + 2 * u := by
      rw [eq1] at eq2
      nlinarith
    -- From the third equation.
    have eq4 : -k * t - u = 1 := by
      nlinarith [hz1, hz2]
    rw [eq1] at eq4
    -- Solving equation.
    have eq5 : k = -5 - 5 * u := by
      linarith
    rw [eq5] at eq3
    -- Rearranged into a quadratic equation.
    have h1 : 5 * u ^ 2 + 7 * u + 2 = 0 := by
      nlinarith
    have h2 : (u + 1) * (5 * u + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- u = -1
      have hu : u = -1 := by
        linarith
      rw [hu] at eq5
      left
      linarith
    · -- u = -2/5
      have hu : u = -2 / 5 := by
        linarith
      rw [hu] at eq5
      right
      linarith
  · -- Assume k = 0 ∨ k = -3, prove the existence of points.
    rintro (hk | hk)
    · -- k = 0, coordinates (1, 2, 4).
      use -1, -1
      use 1, 2, 4
      constructor
      · -- x = 2 + t * 1
        norm_num
        all_goals norm_num [hk]
      constructor
      · -- y = 3 + t * 1
        norm_num
      constructor
      · -- z = 4 + t * (-k)
        norm_num [hk]
      constructor
      · -- x = 1 + u * k
        norm_num [hk]
      constructor
      · -- y = 4 + u * 2
        norm_num
      · -- z = 5 + u * 1
        norm_num
    · -- k = -3, coordinates (11/5, 16/5, 23/5).
      use 1 / 5, -2 / 5
      use 11 / 5, 16 / 5, 23 / 5
      constructor
      · -- x = 2 + t * 1
        norm_num
      constructor
      · -- y = 3 + t * 1
        norm_num
      constructor
      · -- z = 4 + t * (-k)
        norm_num [hk]
      constructor
      · -- x = 1 + u * k
        norm_num [hk]
      constructor
      · -- y = 4 + u * 2
        norm_num
      · -- z = 5 + u * 1
        norm_num