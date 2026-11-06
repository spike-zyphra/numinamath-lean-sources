import Mathlib

theorem algebra_21265 {a b c : ℝ} (h : ∀ x, 3 * x ^ 2 - 24 * x + 72 = a * (x + b) ^ 2 + c) :
    a + b + c = 23 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 4
  ring_nf at eq1 eq2 eq3 eq4
  -- Subtract the first equation from the second to get the first substitution:
  -- a + 2*a*b = -21
  have eq5 : a + 2 * a * b = -21 := by 
    nlinarith
  -- Subtract the second equation from the third to get the second substitution:
  -- 3*a + 2*a*b = -15
  have eq6 : 3 * a + 2 * a * b = -15 := by 
    nlinarith
  -- Solving for a first:
  have ha : a = 3 := by
    linarith
  -- Substituting a = 3 into eq5 to get b
  have hb : b = -4 := by
    rw [ha] at eq5
    nlinarith
  -- Substituting a = 3 and b = -4 into eq1 to get c = 24
  have hc : c = 24 := by 
    rw [ha, hb] at eq1
    nlinarith
  linarith [ha, hb, hc]