import Mathlib

/- George walks 1 mile to school. He leaves home at the same time each day, walks at a steady speed of 3 miles per hour, 
and arrives just as school begins. Today he was distracted by the pleasant weather and walked the first 1/2​ mile at a 
speed of only 2 miles per hour. At how many miles per hour must George run the last 1/2​ mile in order to arrive just as 
school begins today?
(A) 4 (B) 6 (C) 8 (D) 10 (E) 12 -/

theorem algebra_98034 (v : ℝ) (h : 1 / 3 = (1 / 2) / 2 + (1 / 2) / v) : v = 6 := by {
  --We need to solve this linear equation
  calc v = (2 * v) / 2 := by norm_num
       _ = 1 / ((1 / 2) / v) / 2 := by field_simp -- Here, we're modifying the term v to include the above term (1 / 2) / v
       _ = 1 / (1 / 2 / 2 + (1 / 2) / v - 1 / 2 / 2) / 2 := by ring -- Now we modified it further to include the right-hand side of the equation
       _ = 1 / ((1 / 3) - 1 / 2 / 2) / 2 := by rw [h]; -- Plug in equation. This eliminates the variable.
       _ = 6 := by norm_num -- Evaluate the expression.
}