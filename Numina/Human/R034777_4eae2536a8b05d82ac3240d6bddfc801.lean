import Mathlib

open Finset

/- Nancy generates a two-digit integer by rolling a six-sided die twice. The result of her first roll is the tens digit, and the result of her second roll is the ones digit. What is the probability that the resulting integer is divisible by 8? Express your answer as a common fraction. -/
theorem algebra_21743 :
    ((Finset.product (Icc 1 6) (Icc 1 6)).filter (fun x => (x.1 * 10 + x.2) % 8 = 0)).card / (Finset.product (Icc 1 6) (Icc 1 6)).card = (5 : ℚ) / 36 := by
  native_decide
