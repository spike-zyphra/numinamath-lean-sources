import Mathlib

/-
Given $a>b>c>0$, prove that

$$
a^{4} b+b^{4} c+c^{4} a>a b^{4}+b c^{4}+c a^{4} .
$$
-/
theorem inequalities_259385 (a b c : ℝ) (ha : 0 < c) (hc : c < b) (hb : b < a) :
    a^4 * b + b^4 * c + c^4 * a > a * b^4 + b * c^4 + c * a^4 := by

  -- Reorder the ineqalities for convenience.
  have h1 : a > b := hb
  have h2 : b > c := hc
  have h3 : a > c := by linarith
  
  -- An idenitty we will use later.
  have h4 : a^4 * b + b^4 * c + c^4 * a - (a * b^4 + b * c^4 + c * a^4) = (a - b) * (b - c) * (a - c) * (a^2 + b^2 + c^2 + a * b + b * c + c * a) := by
    ring
  
  have h5 : (a - b) * (b - c) * (a - c) * (a^2 + b^2 + c^2 + a * b + b * c + c * a) > 0 := by
    -- All terms in the 4th factor are strictly positive, so it is greater than zero.
    have h6 : a - b > 0 := by linarith
    have h7 : b - c > 0 := by linarith
    have h8 : a - c > 0 := by linarith
    have h9 : a^2 + b^2 + c^2 + a * b + b * c + c * a > 0 := by
      nlinarith [
        mul_pos ha (show 0 < a by nlinarith : a > 0),
        mul_pos ha (show 0 < b by nlinarith : b > 0),
        mul_pos ha (show 0 < c by nlinarith : c > 0)]
    apply mul_pos
    apply mul_pos
    apply mul_pos
    all_goals linarith

  linarith [h4, h5]