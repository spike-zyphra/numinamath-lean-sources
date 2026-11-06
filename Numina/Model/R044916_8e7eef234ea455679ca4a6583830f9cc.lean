import Mathlib

theorem algebra_303554 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (1 / a + 1 / b) / (1 / a - 1 / b) = (a + b) / (b - a) := by 
  by_cases hne : b - a = 0 
  · -- Assume b - a = 0
    have h1 : b = a := by linarith
    have h2 : 1 / a - 1 / b = 0 := by 
      rw [h1]
      field_simp [show a ≠ 0 by linarith]
    rw [h2]
    simp [h1, show a ≠ 0 by linarith]
  · -- Assume b - a ≠ 0 
    have hne1 : 1 / a - 1 / b ≠ 0 := by 
      by_contra h
      have h2 : 1 / a = 1 / b := by 
        linarith
      have h4 : a = b := by 
        field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith] at h2 ⊢ 
        <;> linarith
      have h5 : b - a = 0 := by 
        linarith
      contradiction 
    have hne2 : a ≠ 0 := by linarith 
    have hne3 : b ≠ 0 := by linarith 
    field_simp [hne1, hne2, hne3, hne] 
    <;> ring 
    all_goals linarith