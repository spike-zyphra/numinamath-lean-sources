import Mathlib

/-Sue can either borrow $10,\!000$ dollars for $5$ years with a simple interest of $7\%$ annually or an interest which compounds annually for $6\%$. How much more money, rounded to the nearest dollar, would she have to pay back for the more expensive interest than the less expensive interest?-/
theorem algebra_20051 (P r1 r2 : ℝ) (hP : P = 10000) (hr1 : r1 = 0.07) (hr2 : r2 = 0.06) :
  round ((P + P * r1 * 5) - (P * (1 + r2)^5)) = 118 := by
    -- For the simple interest rate, she would have to pay an interest of $10000 \cdot 0.07=700$ dollars every year. Since there are $5$ years, in the end she would have to pay back $10000+5\cdot 700=13500$ dollars.

    -- For the compounded interest, her balance is multiplied by $1+6\%=1.06$ each year. Therefore, at the end of 5 years her balance is $A=10000(1+0.06)^5=13382.255..$.

    -- The simple interest rate would be more expensive by $13500-13382.255 \approx \boxed{118 \text{ dollars}}$.
    norm_num [hP, hr1, hr2, round]
    have :  Int.fract (117.744224 : ℝ )= 0.744224 := by
      norm_num [Int.fract_eq_iff]
      use 117
      norm_cast
    norm_num at this
    have :  ¬ 2 * Int.fract ((3679507 : ℝ) / 31250) < 1 := by linarith
    simp [this]
    norm_num [Int.ceil_eq_iff]
    aesop
