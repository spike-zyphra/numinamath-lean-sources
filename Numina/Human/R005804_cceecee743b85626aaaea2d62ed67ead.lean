import Mathlib
open Nat Rat

/-
2019 points are chosen independently and uniformly at random on the interval $[0,1]$. Tairitsu picks 1000 of them randomly and colors them black, leaving the remaining ones white. Hikari then computes the sum of the positions of the leftmost white point and the rightmost black point. What is the probability that this sum is at most 1?
-/

-- Number of white points
abbrev num_white_points : ℕ := 1019

-- Number of black points
abbrev num_black_points : ℕ := 1000

-- Total number of points
abbrev num_total_points : ℕ := num_white_points + num_black_points

lemma num_total_points_eq_2019 : num_total_points = 2019 := by
  unfold num_total_points num_white_points num_black_points
  norm_num 
  

-- The probability, according to the solution sketch's argument, that the sum of the
-- position of the leftmost white point and the rightmost black point is at most 1.
-- This is stated to be equal to the probability that the leftmost of all points is white.
def probability_sum_le_one : ℚ :=
  (↑num_white_points : ℚ) / (↑num_total_points : ℚ)

theorem combinatorics_609990 :
    probability_sum_le_one = (1019 : ℚ) / 2019 := by
  unfold probability_sum_le_one
  rw [num_white_points] 
  rw [num_total_points_eq_2019] 
  norm_cast
