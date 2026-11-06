import Mathlib

theorem algebra_8076
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (x : ℝ)
    (h : (x - b - c) / a + (x - a - c) / b + (x - a - b) / c = 3) :
    x = a + b + c := by
  have hne : a ≠ 0 := by linarith
  have hne1 : b ≠ 0 := by linarith
  have hne2 : c ≠ 0 := by linarith
  
  have eq1 : (x - b - c) / a + (x - a - c) / b + (x - a - b) / c = 3 := h
  
  have h2 : (x - b - c) * (b * c) + (x - a - c) * (a * c) + (x - a - b) * (a * b) = 3 * a * b * c := by
  
    have eq24 : (x - b - c) / a + (x - a - c) / b + (x - a - b) / c = ((x - b - c) * (b * c) + (x - a - c) * (a * c) + (x - a - b) * (a * b)) / (a * b * c) := by
      field_simp [hne, hne1, hne2]
      <;> ring
      <;> field_simp [hne, hne1, hne2]
      <;> ring
      
    rw [eq24] at eq1
    have hne0 : a * b * c ≠ 0 := by 
      apply mul_ne_zero
      apply mul_ne_zero
      exact hne
      exact hne1
      exact hne2
      
    field_simp [hne0] at eq1 ⊢
    <;> nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos hb hc]
  all_goals linarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos hb hc]
  all_goals try { nlinarith }
  all_goals try { linarith }
  all_goals try { nlinarith }
  all_goals try { linarith }