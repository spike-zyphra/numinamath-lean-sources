import Mathlib

open Nat Finset

/-Julia is learning how to write the letter C. She has 6 differently-colored crayons, and wants to write Cc Cc Cc Cc Cc . In how many ways can she write the ten Cs , in such a way that each upper case C is a different color, each lower case C is a different color, and in each pair the upper case C and lower case C are different colors?
-/
abbrev ways_to_color_upper_Cs : ℕ :=
  factorial 6
-- The problem statement uses D_n for natural numbers, so we'd want derangement_rec k ≥ 0.
-- For n ≥ 2, D_n = (n-1)(D_{n-1} + D_{n-2})
-- D_0 = 1, D_1 = 0
-- D_2 = (2-1)(D_1 + D_0) = 1 * (0 + 1) = 1
-- D_3 = (3-1)(D_2 + D_1) = 2 * (1 + 0) = 2
-- D_4 = (4-1)(D_3 + D_2) = 3 * (2 + 1) = 9
-- D_5 = (5-1)(D_4 + D_3) = 4 * (9 + 2) = 4 * 11 = 44
-- D_6 = (6-1)(D_5 + D_4) = 5 * (44 + 9) = 5 * 53 = 265

-- This recursive definition is purely in Nat and matches the values.
def D_nat : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n+2 => (n+1) * (D_nat (n+1) + D_nat n)

lemma D_nat_5 : D_nat 5 = 44 := by rfl
lemma D_nat_6 : D_nat 6 = 265 := by rfl

def ways_to_color_lower_Cs_per_upper_coloring_comp : ℕ :=
  D_nat 6 + D_nat 5

lemma ways_to_color_lower_Cs_per_upper_coloring_comp_val : ways_to_color_lower_Cs_per_upper_coloring_comp = 309 := by
  unfold ways_to_color_lower_Cs_per_upper_coloring_comp
  rw [D_nat_5, D_nat_6]

def total_ways_to_color_Cs_comp : ℕ :=
  ways_to_color_upper_Cs * ways_to_color_lower_Cs_per_upper_coloring_comp

theorem final_answer_is_222480_comp : total_ways_to_color_Cs_comp = 222480 := by
  unfold total_ways_to_color_Cs_comp 
  rw [ways_to_color_lower_Cs_per_upper_coloring_comp_val]
  rfl
