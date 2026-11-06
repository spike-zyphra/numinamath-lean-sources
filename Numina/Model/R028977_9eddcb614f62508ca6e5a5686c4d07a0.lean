import Mathlib

theorem inequalities_597564 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 4 ≤ a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) +
    c / ((c + 1) * (a + 1)) := by
  -- We need to show:
  -- \frac{a}{(a+1)(b+1)} + \frac{b}{(b+1)(c+1)} + \frac{c}{(c+1)(a+1)} \geqslant \frac{3}{4}

  have h1 : 0 < (a + 1) * (b + 1) * (c + 1) := by
    positivity

  have h2 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) =
      (a * (c + 1) + b * (a + 1) + c * (b + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
    field_simp
    ring
  rw [h2]
  have h3 : (3 / 4 : ℝ) ≤ (a * (c + 1) + b * (a + 1) + c * (b + 1)) / ((a + 1) * (b + 1) * (c + 1)) :=
    by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        habc]
  linarith