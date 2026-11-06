import Mathlib

theorem algebra_302841 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 = b * (b + c)) (h2 : b^2 = c * (c + a)) :
    1 / c = 1 / a + 1 / b := by
  -- From h1: a^2 = b(b + c), we rewrite as a^2 = b^2 + bc
  -- From h2: b^2 = c(c + a), we rewrite as b^2 = c^2 + ac

  -- Adding these two equations: a^2 + b^2 = b^2 + bc + c^2 + ac
  -- Simplifying: a^2 = c^2 + bc + ac
  -- Hence: a^2 - c^2 = bc + ac
  -- We can factor this as (a - c)(a + c) = c(b + a)
  have eq3 : a^2 - c^2 = c * (a + b) := by
    nlinarith
  -- We need to prove $\frac{1}{c} = \frac{1}{a} + \frac{1}{b}$ which is equivalent to $\frac{a + b}{ab} = \frac{1}{c}$.
  -- This is equivalent to proving $ab = c(a + b)$.
  have eq4 : a * b = c * (a + b) := by
    nlinarith [h1, h2]
  
  have h6 : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
  
  -- Using eq4: $a * b = c * (a + b)$, we can write $\frac{1}{c} = \frac{a + b}{a * b} = \frac{1}{a} + \frac{1}{b}$.
  field_simp [h6, show c ≠ 0 by positivity]
  nlinarith [eq4]
  all_goals positivity