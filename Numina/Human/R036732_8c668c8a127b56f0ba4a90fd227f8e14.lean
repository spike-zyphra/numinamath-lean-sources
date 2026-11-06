import Mathlib

theorem inequalities_616699 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 + a + b + c = 2 * a * b * c) :
    3 / 2 ≤ a * b / (1 + a + b : ℚ) + b * c / (1 + b + c : ℚ) +
    c * a / (1 + c + a : ℚ) := by 
  have h1 : a ≤ 3 := by 
    by_cases h2 : a ≤ 3
    · exact h2
    · -- Suppose a > 3
      have h3 : 2 * a * b * c > 1 + a + b + c := by nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      omega
  have h2 : b ≤ 3 := by 
    by_cases h3 : b ≤ 3
    · exact h3
    · -- Suppose b > 3
      have h4 : 2 * a * b * c > 1 + a + b + c := by nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      omega
  have h3 : c ≤ 3 := by 
    by_cases h4 : c ≤ 3
    · exact h4
    · -- Suppose c > 3
      have h5 : 2 * a * b * c > 1 + a + b + c := by nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      omega
  interval_cases a <;> 
  interval_cases b <;> 
  interval_cases c <;> 
    norm_num at h ⊢ <;> 
    all_goals { 
      norm_num at h ⊢ 
      <;> linarith 
    }