import Mathlib

theorem inequalities_4714 (a b : ℝ) (ha : 3 < a ∧ a < 4) (hb : 4 < b ∧ b < 5) :
    3/5 < a/b ∧ a/b < 1 := by
  have ha1 : 3 < a := ha.1
  have ha2 : a < 4 := ha.2
  have hb1 : 4 < b := hb.1
  have hb2 : b < 5 := hb.2
  have h1 : 0 < b := by linarith
  -- For $\frac{3}{5} < \frac{a}{b}$:
  -- Cross-multiplying (since $b > 0$), we get $3b < 5a$.
  -- $a > 3$ and $b < 5$: $3b < 3 \cdot 5 = 15$ and $5a > 5 \cdot 3 = 15$.
  have h2 : 3 * b < 5 * a := by
    linarith
  -- For $\frac{a}{b} < 1$:
  -- Cross-multiplying (since $b > 0$), we get $a < b$.
  -- $a < 4$ and $b > 4$: $a < 4 < b$.
  have h3 : a < b := by
    linarith
  -- Show that $\frac{3}{5} < \frac{a}{b}$
  have h4 : 3/5 < a/b := by
    have pos1 : 0 < b := by linarith
    apply (lt_div_iff' (by positivity)).mpr
    linarith
  -- Show that $\frac{a}{b} < 1$
  have h7 : a/b < 1 := by
    have pos1 : 0 < b := by linarith
    -- Since a < b, then (a)/b < (b)/b = 1
    have h8 : a < b := by linarith
    have h9 : a / b < b / b := by
      apply (div_lt_div_right (by positivity)).mpr
      linarith
    have h10 : b / b = 1 := by
      field_simp
    -- Now we can substitute and complete the inequality
    linarith
  constructor
  · exact h4
  · exact h7