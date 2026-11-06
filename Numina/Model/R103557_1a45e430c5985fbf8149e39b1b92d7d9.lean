import Mathlib

theorem inequalities_597561 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) ∧
    (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b)) ≥ (a + b + c) / 2 := by 
  constructor
  · -- Prove the first inequality: $\frac{a}{b+c} + \frac{b}{c+a} + \frac{c}{a+b} \geq \frac{3}{2}$
    have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by 
      have hb1 : 0 < b + c := by linarith
      have ha1 : 0 < a + b := by linarith
      have hc1 : 0 < c + a := by linarith
      have h2 : 0 < (b + c) * (c + a) * (a + b) := by positivity 
      have h3 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) = 
        ( (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a)) - 3 / 2 * (b + c) * (c + a) * (a + b) ) / ((b + c) * (c + a) * (a + b)) := by 
        field_simp 
        ring 
      rw [h3]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      all_goals positivity 
    linarith 
  · -- Prove the second inequality: $\frac{a ^ 2}{b + c} + \frac{b ^ 2}{c + a} + \frac{c ^ 2}{a + b} \geq \frac{a + b + c}{2}$
    have h2 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 ≥ 0 := by 
      have hb1 : 0 < b + c := by linarith
      have ha1 : 0 < a + b := by linarith
      have hc1 : 0 < c + a := by linarith 
      have h2 : 0 < (b + c) * (c + a) * (a + b) := by positivity 
      have h3 : (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 ) 
        = ( (a ^ 2 * (c + a) * (a + b) + b ^ 2 * (b + c) * (a + b) + c ^ 2 * (b + c) * (c + a) ) - (a + b + c) / 2 * (b + c) * (c + a) * (a + b) ) / ((b + c) * (c + a) * (a + b)) := by 
        field_simp 
        ring 
      rw [h3]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      all_goals positivity 
    linarith