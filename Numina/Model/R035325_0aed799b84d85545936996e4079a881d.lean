import Mathlib

theorem algebra_16668 (b c : ℝ) {h : {x | abs (x - 5) = 2} = {x | x ^ 2 + b * x + c = 0}} :
    (b, c) = (-10, 21) := by
  have h1 : (3 : ℝ) ∈ {x | abs (x - 5) = 2} := by
    norm_num [abs_eq]
  have h2 : (3 : ℝ) ∈ {x | x ^ 2 + b * x + c = 0} := by
    rw [h] at *
    exact h1
  -- 7 is in the solution set
  have h3 : (7 : ℝ) ∈ {x | abs (x - 5) = 2} := by
    norm_num [abs_eq]
  -- so 7 is a root of the quadratic
  have h4 : (7 : ℝ) ∈ {x | x ^ 2 + b * x + c = 0} := by
    rw [h] at *
    exact h3
  -- simplify the set membership conditions
  simp at h2 h4
  -- Now we have two equations:
  -- 9 + 3 * b + c = 0
  -- 49 + 7 * b + c = 0
  -- We need to solve them.
  have eq1 : 9 + 3 * b + c = 0 := by 
    linarith 
  have eq2 : 49 + 7 * b + c = 0 := by 
    linarith
  -- solve the equations
  -- first, subtract eq1 from eq2
  have eqb : b = -10 := by
    nlinarith
  -- then, substitute b = -10 into eq1
  have eqc : c = 21 := by
    rw [eqb] at eq1
    linarith
  -- Now we can compute the ordered pair
  simp [Prod.ext_iff, eqb, eqc]