import Mathlib

/- Each day, Jenny ate 20% of the jellybeans that were in her jar at the beginning of that day. 
At the end of the second day, 32 remained. 
How many jellybeans were in the jar originally?
(A) 40(B) 50(C) 55(D) 60(E) 75 -/
theorem algebra_93561 {x : ℕ} (hx : x ≠ 0) (h1 : (1 - 20 / 100 : ℝ) * (1 - 20 / 100 : ℝ) * x = 32) :
x = 50 := by
  --by hypotheses we have that 0.8*0.8*x = 32. Then solve the equation for x.
  field_simp at h1
  norm_num at h1
  have h := congrFun (congrArg HMul.hMul h1) (1/6400)
  ring_nf at h
  rify
  exact h