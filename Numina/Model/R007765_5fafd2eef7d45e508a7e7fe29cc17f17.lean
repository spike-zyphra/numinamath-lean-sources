import Mathlib
open Mathlib

lemma algebra_1153 (x y : ℝ) (h1 : 2 = (10 : ℝ) / (100 : ℝ) * x) (h2 : 2 = (20 : ℝ) / (100 : ℝ) * y) : x - y = 10 := by
  have hx : x = 20 := by 
    linarith 
  have hy : y = 10 := by 
    linarith 
  rw [hx, hy]
  norm_num