import Mathlib
open Mathlib

lemma algebra_1181 (inheritance : ℚ) (totalTax : (20 : ℚ) / 100 * inheritance + (inheritance - (20 : ℚ) / 100 * inheritance) * (10 : ℚ) / 100 = 10500) : inheritance = 37500 := by 
  linarith