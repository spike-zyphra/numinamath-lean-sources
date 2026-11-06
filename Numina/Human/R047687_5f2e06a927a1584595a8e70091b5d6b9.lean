import Mathlib

/- If the real numbers $a, b, c, d$ are such that $0<a, b, c, d<1$, show that

$$
1+a b+b c+c d+d a+a c+b d>a+b+c+d
$$ -/
theorem inequalities_604693 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) (h4 : d < 1) :
    1 + a * b + b * c + c * d + d * a + a * c + b * d > a + b + c + d := by
  -- Consider cases 1 ≥ a + b + c and 1 < a + b + c.
  cases le_or_lt (a + b + c) 1 with
  | inl h =>
    -- If 1 ≥ a + b + c, Use the fact that 1 ≥ a + b + c, 1 < d and ab, bc, ca > 0 to prove the inequality.
    nlinarith only [ha, hb, hc, hd, h4, h]
  | inr h =>
    -- If 1 < a + b + c.
    -- Show that d * (a + b + c) > d.
    have h5 : d * (a + b + c) > d := by
      nlinarith only [hd, h]
    -- Show that 1 + ab + bc + ca > a + b + c.
    have h6 : 1 - (a + b + c) + a * b + b * c + c * a > 0 := by
      calc
        1 - (a + b + c) + a * b + b * c + c * a > a * b * c := by
          -- This inequality is equivalent to (1 - a)(1 - b)(1 - c) > 0.
          replace h1 : 1 - a > 0 := by
            linarith only [h1]
          replace h2 : 1 - b > 0 := by
            linarith only [h2]
          replace hc : 1 - c > 0 := by
            linarith only [h3]
          linarith only [show 0 < (1 - a) * (1 - b) * (1 - c) by positivity]
        _ > 0 := by
          positivity
    -- Combine the two inequalities above.
    linarith only [h5, h6]
