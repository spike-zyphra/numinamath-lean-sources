import Mathlib

/- Let $a,b,c>0$ and $abc\ge1.$ Prove that $a^4+b^3+c^2\ge a^3+b^2+c.$ -/
theorem inequalities_91135 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c ≥ 1) :
    a ^ 4 + b ^ 3 + c ^ 2 ≥ a ^ 3 + b ^ 2 + c := by 
  -- Consider the inequality involving geometric mean conditions with squares.
  nlinarith [sq_nonneg (a ^ 2 - b), 
             sq_nonneg (b ^ 2 - c), 
             sq_nonneg (a ^ 2 - c), 
             sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
             -- derive from the positivity of products such as essential targets and rearrangements
             sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]