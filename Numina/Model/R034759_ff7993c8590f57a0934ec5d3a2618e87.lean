import Mathlib

/- Let $a . b$ c ce positue real numbers such that $a+b+c=a^{2}+b^{2}+c^{2}$. Shou that

$$
\frac{a^{2}}{a^{2}+a b}+\frac{b^{2}}{b^{2}+b c}+\frac{c^{2}}{c^{2}+c a} \geq \frac{a+b+c}{2}
$$ -/

-- Main theorem: Proves the inequality for positive real numbers a, b, c satisfying the given condition
theorem algebra_604456 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = a ^ 2 + b ^ 2 + c ^ 2) :
  a ^ 2 / (a ^ 2 + a * b) + b ^ 2 / (b ^ 2 + b * c) + c ^ 2 / (c ^ 2 + c * a) ≥ (a + b + c) / 2:= by 
  have h4 : a ^ 2 / (a ^ 2 + a * b) = a / (a + b) := by 
    have ha1 : a ^ 2 + a * b = a * (a + b) := by 
      ring
    rw [ha1]
    field_simp
    all_goals nlinarith
  have h5 : b ^ 2 / (b ^ 2 + b * c) = b / (b + c) := by 
    have hb1 : b ^ 2 + b * c = b * (b + c) := by 
      ring 
    rw [hb1]
    field_simp 
    all_goals nlinarith 
  have h6 : c ^ 2 / (c ^ 2 + c * a) = c / (c + a) := by 
    have hc1 : c ^ 2 + c * a = c * (c + a) := by 
      ring 
    rw [hc1]
    field_simp 
    all_goals nlinarith 
  rw [h4, h5, h6]
  have pos1 : 0 < a + b := by linarith 
  have pos2 : 0 < b + c := by linarith 
  have pos3 : 0 < c + a := by linarith 
  have h7 : a / (a + b) + b / (b + c) + c / (c + a) ≥ (a + b + c) / 2 := by
    have h8 : a / (a + b) + b / (b + c) + c / (c + a) - (a + b + c) / 2 ≥ 0 := by 
      have h9 : a / (a + b) + b / (b + c) + c / (c + a) - (a + b + c) / 2 =
          (2 * a * (b + c) * (c + a) + 2 * b * (a + b) * (c + a) + 2 * c * (a + b) * (b + c) - (a + b + c) * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a)) := by
        field_simp 
        ring 
      rw [h9] at *
      apply div_nonneg 
      · -- Prove the numerator is positive.
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
          mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
          mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity), 
          h
        ]
      all_goals 
        positivity 
    linarith 
  linarith