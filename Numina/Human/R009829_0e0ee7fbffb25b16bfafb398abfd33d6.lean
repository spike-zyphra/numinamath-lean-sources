import Mathlib

/- Corn costs 99 cents per pound, and beans cost 45 cents per pound. If Shea buys 24 total pounds of corn and beans, and it costs $\$18.09$, how many pounds of corn did Shea buy? Express your answer as a decimal to the nearest tenth. -/
theorem algebra_14591 {x y : ℝ} (hx : x + y = 24) (hy : 99*x+45*y=1809) :
    x=13.5 := by 
  apply Eq.symm
  ring_nf at hx hy ⊢
  nlinarith