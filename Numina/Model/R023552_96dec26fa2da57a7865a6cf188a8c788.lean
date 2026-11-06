import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_185833 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a > b) (f : ℝ → ℝ) (hf : f = λ x => a * sqrt (1 - x ^ 2 / b ^ 2))
  (g : ℝ → ℝ) (hg : g = λ x => b * sqrt (1 - x ^ 2 / a ^ 2)) (h1 : f 1 = b * sqrt (1 - 1 ^ 2 / a ^ 2))
  (h2 : g 1 = a * sqrt (1 - 1 ^ 2 / b ^ 2)) (h3 : f 0 = b * sqrt (1 - 0 ^ 2 / a ^ 2))
  (h4 : g 0 = a * sqrt (1 - 0 ^ 2 / b ^ 2)) (h5 : f (-1) = b * sqrt (1 - (-1) ^ 2 / a ^ 2))
  (h6 : g (-1) = a * sqrt (1 - (-1) ^ 2 / b ^ 2)) (h7 : f (-1) = b * sqrt (1 - (-1) ^ 2 / a ^ 2))
  (h8 : g (-1) = a * sqrt (1 - (-1) ^ 2 / b ^ 2)) (h9 : f 1 = b * sqrt (1 - 1 ^ 2 / a ^ 2))
  (h10 : g 1 = a * sqrt (1 - 1 ^ 2 / b ^ 2)) (h11 : f 0 = b * sqrt (1 - 0 ^ 2 / a ^ 2))
  (h12 : g 0 = a * sqrt (1 - 0 ^ 2 / b ^ 2)) (h13 : f (-1) = b * sqrt (1 - (-1) ^ 2 / a ^ 2))
  (h14 : g (-1) = a * sqrt (1 - (-1) ^ 2 / b ^ 2)) (h15 : f 1 = b * sqrt (1 - 1 ^ 2 / a ^ 2))
  (h16 : g 1 = a * sqrt (1 - 1 ^ 2 / b ^ 2)) (h17 : f 0 = b * sqrt (1 - 0 ^ 2 / a ^ 2))
  (h18 : g 0 = a * sqrt (1 - 0 ^ 2 / b ^ 2)) (h19 : f (-1) = b * sqrt (1 - (-1) ^ 2 / a ^ 2))
  (h20 : g (-1) = a * sqrt (1 - (-1) ^ 2 / b ^ 2)) :
  ∫ x in (-1)..1, (2 * π * x * (a * sqrt (1 - x ^ 2 / b ^ 2)) * (b * sqrt (1 - x ^ 2 / a ^ 2))) = 4 / 3 ^ 2 * b * lambda := by 
  aesop