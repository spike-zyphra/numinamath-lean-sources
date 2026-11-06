import Mathlib

open Finset

/-Bob is coloring lattice points in the coordinate plane. Find the number of ways Bob can color five points in 
{(x,y)∣1≤x,y≤5} blue such that the distance between any two blue points is not an integer.-/

theorem combinatorics_609984 :
  ((Icc (1: ℤ) 1 ×ˢ Icc (1: ℤ) 5 ×ˢ Icc (2: ℤ) 2 ×ˢ Icc (1: ℤ) 5 ×ˢ Icc (3: ℤ) 3
  ×ˢ Icc (1: ℤ) 5 ×ˢ Icc (4: ℤ) 4 ×ˢ Icc (1: ℤ) 5 ×ˢ Icc (5: ℤ) 5 ×ˢ Icc (1: ℤ) 5).filter
  (fun (x1, y1, x2, y2, x3, y3, x4, y4, x5, y5) =>
  ¬ (IsSquare ((x1 - x2)^2 + (y1 - y2)^2) ∨
    IsSquare ((x1 - x3)^2 + (y1 - y3)^2) ∨
    IsSquare ((x1 - x4)^2 + (y1 - y4)^2) ∨
    IsSquare ((x1 - x5)^2 + (y1 - y5)^2) ∨
    IsSquare ((x2 - x3)^2 + (y2 - y3)^2) ∨
    IsSquare ((x2 - x4)^2 + (y2 - y4)^2) ∨
    IsSquare ((x2 - x5)^2 + (y2 - y5)^2) ∨
    IsSquare ((x3 - x4)^2 + (y3 - y4)^2) ∨
    IsSquare ((x3 - x5)^2 + (y3 - y5)^2) ∨
    IsSquare ((x4 - x5)^2 + (y4 - y5)^2)))).card = 80 := by

    native_decide
  