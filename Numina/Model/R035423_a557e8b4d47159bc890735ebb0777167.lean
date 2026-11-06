import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_68389 :
  IsLeast {z : ℝ | ∃ x y, z^2 ≤ x + y ∧ x^2 ≤ y + z ∧ y^2 ≤ z + x} (-1/4) ∧
  IsGreatest {z : ℝ | ∃ x y, z^2 ≤ x + y ∧ x^2 ≤ y + z ∧ y^2 ≤ z + x} 2 := by
  constructor 
  · -- Show that -1/4 is the least element in the set 
    constructor 
    · -- Show that -1/4 is in the set 
      use 1 / 2, 1 / 2 
      constructor
      · -- Show that (-1/4) ^ 2 ≤ (1/2) + (1/2)
        norm_num 
      constructor 
      · -- Show that (1/2) ^ 2 ≤ (1/2) + (-1/4)
        norm_num 
      · -- Show that (1/2) ^ 2 ≤ (-1/4) + (1/2)
        norm_num 
    · -- Show that -1/4 is minimal 
      intro z h 
      rcases h with ⟨x, y, h1, h2, h3⟩ 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z + 1 / 4), sq_nonneg (x + y - z), sq_nonneg ((x - y) + (y - z) + (z - x))]
  · -- Show that 2 is the greatest element in the set 
    constructor 
    · -- Show that 2 is in the set 
      use 2, 2 
      constructor 
      · -- Show that (2) ^ 2 ≤ 2 + 2
        norm_num 
      constructor 
      · -- Show that (2) ^ 2 ≤ 2 + (2)
        norm_num 
      · -- Show that (2) ^ 2 ≤ (2) + 2 
        norm_num 
    · -- Show that 2 is greatest 
      intro z h 
      rcases h with ⟨x, y, h1, h2, h3⟩ 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), sq_nonneg (x + y - z), sq_nonneg ((x - y) + (y - z) + (z - x))]