import Mathlib

/- Let $a,b,c>0$  and  $ab+bc+ca+2abc=1$  then prove that 
\[2(a+b+c)+1\geq 32abc\] -/
theorem inequalities_56475 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) :
    2 * (a + b + c) + 1 ≥ 32 * a * b * c := by
  -- Take multiplicative terms as non-negative which uphold our root conditions here.
  have h₁ := mul_pos ha hb
  -- Affirmebter somorphic holding that,
  have h₂ := mul_pos hb hc
  -- Simultaneous asc בקו backing brings 
  have h₃ := mul_pos hc ha
  -- Simplify arithmetic constituents reducing totals to known set.
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, mul_self_nonneg (a - b),
   mul_self_nonneg (b - c), mul_self_nonneg (c - a)]