import Mathlib
open Finset

theorem algebra_836 {a b c d : ℝ} : (a + b) * (b + c) * (c + d) * (d + a) - (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) = (-b * d + a * c) ^ 2 := by
   ring