import Mathlib

open Nat

theorem algebra_11296 : ⌊(Nat.factorial 2007 + Nat.factorial 2004 : ℝ) / (Nat.factorial 2006 + Nat.factorial 2005)⌋ = 2006 := by

  have h4 : (Nat.factorial 2007 + Nat.factorial 2004 : ℝ) = (Nat.factorial 2004 : ℝ) * ((2007 * 2006 * 2005 + 1) : ℝ) := by
    have h1' : (Nat.factorial 2007 : ℝ) = (2007 : ℝ) * (2006 : ℝ) * (2005 : ℝ) * (Nat.factorial 2004 : ℝ) := by
      have h_1 : (Nat.factorial 2007 : ℝ) = (2007 : ℝ) * (Nat.factorial 2006 : ℝ) := by
        exact_mod_cast (show Nat.factorial 2007 = 2007 * Nat.factorial 2006 by rw [Nat.factorial_succ])
      have h_2 : (Nat.factorial 2006 : ℝ) = (2006 : ℝ) * (Nat.factorial 2005 : ℝ) := by
        exact_mod_cast (show Nat.factorial 2006 = 2006 * Nat.factorial 2005 by rw [Nat.factorial_succ])
      have h_3 : (Nat.factorial 2005 : ℝ) = (2005 : ℝ) * (Nat.factorial 2004 : ℝ) := by
        exact_mod_cast (show Nat.factorial 2005 = 2005 * Nat.factorial 2004 by rw [Nat.factorial_succ])
      rw [h_1, h_2, h_3]
      all_goals ring

    have h7 : (Nat.factorial 2004 : ℝ) = (Nat.factorial 2004 : ℝ) := rfl
    nlinarith [h1']

  have h5 : (Nat.factorial 2006 + Nat.factorial 2005 : ℝ) = (Nat.factorial 2004 : ℝ) * ((2005 * 2007) : ℝ) := by
    have h_1 : (Nat.factorial 2006 : ℝ) = (2006 : ℝ) * (Nat.factorial 2005 : ℝ) := by
      exact_mod_cast (show Nat.factorial 2006 = 2006 * Nat.factorial 2005 by rw [Nat.factorial_succ])
    have h_2 : (Nat.factorial 2005 : ℝ) = (2005 : ℝ) * (Nat.factorial 2004 : ℝ) := by
      exact_mod_cast (show Nat.factorial 2005 = 2005 * Nat.factorial 2004 by rw [Nat.factorial_succ])
    rw [h_1, h_2]
    all_goals ring

  rw [h4, h5]

  have h6 : (Nat.factorial 2004 : ℝ) > 0 := by
    positivity

  have h7 : (Nat.factorial 2004 : ℝ) ≠ 0 := by
    linarith [h6]

  have h8 : ((Nat.factorial 2004 : ℝ) * ((2007 * 2006 * 2005 + 1) : ℝ) ) / ((Nat.factorial 2004 : ℝ) * ((2005 * 2007) : ℝ)) =
      ((2007 * 2006 * 2005 + 1) : ℝ) / ((2005 * 2007) : ℝ) := by
    have h7' : (Nat.factorial 2004 : ℝ) ≠ 0 := h7
    field_simp [h7']
    all_goals ring

  rw [h8]

  have h9 : ((2007 * 2006 * 2005 + 1) : ℝ) / ((2005 * 2007) : ℝ) = (2006 + (1 / (2005 * 2007)) : ℝ) := by
    field_simp
    all_goals ring

  rw [h9]

  norm_num [Int.floor_eq_iff]