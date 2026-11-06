import Mathlib

theorem algebra_98959
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h1 : a * b + a + b = 35)
    (h2 : b * c + b + c = 35)
    (h3 : c * a + c + a = 35) :
    (a + 1) * (b + 1) * (c + 1) = 216 := by

  -- Use given equations to create (a+1)(b+1) = 36, (b+1)(c+1) = 36, (c+1)(a+1) = 36

  have eq1 : (a + 1) * (b + 1) = 36 := by
    nlinarith
  
  have eq2 : (b + 1) * (c + 1) = 36 := by
    nlinarith

  have eq3 : (c + 1) * (a + 1) = 36 := by
    nlinarith
  
  -- Note that (a+1)(b+1)(c+1) is the product of the three terms, so we multiply them all

  -- Now we want to calculate (a+1)(b+1)(c+1).
  
  -- (a+1)(b+1)(c+1) = sqrt( (a+1)(b+1) * (b+1)(c+1) * (c+1)(a+1) ) 

  -- But we can compute in Lean 4 using algebra constraints:

  have h4 : (a + 1) * (b + 1) * (c + 1) = 216 := by
    nlinarith [sq_nonneg (a + 1 - (b + 1)), sq_nonneg (b + 1 - (c + 1)), sq_nonneg (c + 1 - (a + 1))]
  
  exact h4