import Mathlib
open Real

/- The expression √(4/3)-√(3/4)  is equal to:
(A) √3/6 (B) -√3/6 (C) √-3/6 (D) 5√3/6 (E) 1 -/
theorem algebra_93094 : Real.sqrt (4 / 3) - Real.sqrt (3 / 4) = Real.sqrt 3 / 6 := by
  -- first we obtain the lemma reducing √4 to 2
  have sq4:√4=2:= by rw[((by norm_num):(4:ℝ)=2*2)];simp
  -- focusing the main goal, we reduce all the divisions
  field_simp
  -- change the multiplication order to pair the two √3s
  rw[← mul_assoc]
  -- reducing the square roots √3 and √4
  simp only [sq4]
  -- calculating the both sides of the goal to show they're the same
  norm_num