import Mathlib

theorem algebra_287723 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : (a * 8 + b * 2 + c * 2) / 10 = (b * 8 + a * 2 + c * 2) / 10 + 1)
    (h2 : (a * 2 + b * 8 + c * 2) / 10 = (a * 8 + b * 2 + c * 2) / 10 + 1)
    (h3 : a = 12) :
    (a = 12 ∧ b = 17 ∧ c = 22) ∨ (a = 7 ∧ b = 12 ∧ c = 17) ∨ (a = 2 ∧ b = 7 ∧ c = 12) := by
  have h4 : 8 * a + 2 * b + 2 * c = 8 * b + 2 * a + 2 * c + 10 := by 
    linarith [h1]
  have h5 : 2 * a + 8 * b + 2 * c = 8 * a + 2 * b + 2 * c + 10 := by 
    linarith [h2]
  -- Clear denominators and substitute h3 into the equations.
  -- This will lead to contradictions with the given conditions, orders, and given h3.
  -- Thus, the existence theorem gives false so conclusion is trivial.
  -- A field may have a different meaning, i.e., mutual positivity, but in this case, the method works as expected.
  linarith [h3]