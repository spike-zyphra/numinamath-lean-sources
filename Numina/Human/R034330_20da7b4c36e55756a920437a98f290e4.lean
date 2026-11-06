import Mathlib
/- The formula to convert Celsius to Fahrenheit is

$$
F^{\circ}=1.8 \cdot C^{\circ}+32
$$

In Celsius, it is $10^{\circ}$ warmer in New York right now than in Boston. In Fahrenheit, how much warmer is it in New York than in Boston? -/
theorem algebra_610636 (NF NC BF BC : ℝ) (hN : NF = 1.8 * NC + 32) (hB : BF = 1.8 * BC + 32) (h : NC = 10 + BC): NF = BF + 18:= by
  -- Substitute the given values into the equations
  norm_num at hN hB h
  -- use linarith to solve the equation
  linarith
