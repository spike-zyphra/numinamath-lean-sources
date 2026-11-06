import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_161120 :
  IsLeast {t : ℝ | ∃ x y z, t = x^2 + y^2 + z^2 ∧ x * (0 : ℝ) + y * (-Real.sqrt 3 / 2) + z * (Real.sqrt 3 / 2) = 1 ∧
    x * 1 + y * (-1 / 2) + z * (-1 / 2) = 2} (10 / 3) := by
  constructor
  · -- Show 10/3 is in the set
    use 4 / 3, (-2 - Real.sqrt 3) / 3, (-2 + Real.sqrt 3) / 3
    constructor
    · -- Show that the sum of squares is 10/3
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
    constructor
    · -- Show that the first equation is satisfied
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
    · -- Show that the second equation is satisfied
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
  · -- Show that no smaller element is in the set
    intro t ht
    rcases ht with ⟨x, y, z, ht1, h1, h2⟩
    have eq1 : z - y = 2 * Real.sqrt 3 / 3 := by
      have eq1 : Real.sqrt 3 > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have eq2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [h1, eq2]
    have eq2 : z = y + 2 * Real.sqrt 3 / 3 := by
      linarith [eq1]
    have eq3 : x = 2 + (1 / 2) * y + (1 / 2) * z := by
      linarith [h2]
    have eq4 : x = 2 + y + Real.sqrt 3 / 3 := by
      rw [eq2] at eq3
      linarith [eq3]
    have ht2 : t = (2 + y + Real.sqrt 3 / 3) ^ 2 + y ^ 2 + (y + 2 * Real.sqrt 3 / 3) ^ 2 := by
      rw [ht1]
      rw [eq4, eq2]
      all_goals nlinarith
    have h3 : t ≥ 10 / 3 := by
      rw [ht2]
      nlinarith [sq_nonneg (y + (2 + Real.sqrt 3) / 3), sq_nonneg (x - 4 / 3), sq_nonneg ((y + 2 * Real.sqrt 3 / 3) + (2 - Real.sqrt 3) / 3), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    linarith