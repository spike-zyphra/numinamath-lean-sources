import Mathlib

/- $⌊n⌋$ represents the greatest integer less than or equal to $n$, whether $n$ is positive or negative, such as $ ⌊ 5 . 8⌋ = 5 $, $ ⌊ - 2 . 4⌋ = - 3 $. Find the value of $ ⌊\frac { ⌊ \frac { 2 8 } { 3 } ⌊ + ⌊ \frac { 9 } { 5 } ⌊ + 6 } { 8 - ⌊\frac { 3 2 } { 5 } ⌊ }⌋ $.

$⌊n⌋$ represents the greatest integer less than or equal to $n$, whether $n$ is positive or negative, such as $ ⌊ 5 . 8⌋ = 5 $, $ ⌊ - 2 . 4⌋ = - 3 $. Find the value of $ ⌊\frac { ⌊ \frac { 2 8 } { 3 } ⌊ + ⌊ \frac { 9 } { 5 } ⌊ + 6 } { 8 - ⌊\frac { 3 2 } { 5 } ⌊ }⌋ $. -/
theorem number_theory_5397 : ⌊(⌊(28/3 : ℝ)⌋ + ⌊(9/5 : ℝ)⌋ + 6)/ (8 - ⌊(32/5 : ℝ)⌋)⌋ = 8 := by 
  norm_num [Int.floor_eq_iff]