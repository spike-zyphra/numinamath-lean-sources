import Mathlib

theorem number_theory_314944 (a b c : ℕ) (ha : a ≠ 0) (h : a < 10) (h' : b < 10) (h'' : c < 10)
    (h''' : 100 * a + 10 * c + b + 100 * b + 10 * a + c + 100 * b + 10 * c + a +
      100 * c + 10 * a + b + 100 * c + 10 * b + a = 3194) :
    100 * a + 10 * b + c = 358 := by
  -- First, we recognize the equation can be transformed
  -- The given equation is sum of 5 numbers: (a c b) + (b a c) + (b c a) + (c a b) + (c b a) = 3194
  -- Expanding this, we collect coefficients
  -- For a: 100*a + 10*a + a + 10*a + a = 122*a
  -- For b: b + 100*b + 100*b + b + 10*b = 212*b
  -- For c: 10*c + c + 10*c + 100*c + 100*c = 221*c
  have eq1 : 122 * a + 212 * b + 221 * c = 3194 := by
    omega
  -- Next, we need to solve this equation with the constraints of digits
  -- The original number is 100*a + 10*b + c
  -- Since all variables are bounded between 0-9, with a > 0
  -- We can use exhaustive search to find the answer
  have ha1 : a ≤ 9 := by omega
  have hb1 : b ≤ 9 := by omega
  have hc1 : c ≤ 9 := by omega
  interval_cases a <;> interval_cases b <;> omega