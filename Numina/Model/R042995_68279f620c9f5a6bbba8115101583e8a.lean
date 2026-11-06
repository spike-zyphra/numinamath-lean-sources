import Mathlib
theorem algebra_13505 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + d = b ∧ b + d = c) (h1 : a * b * c = 64) :
    b ≥ 4 := by 
  rcases h with ⟨h2, h3⟩
  have h2' : a = b - d := by linarith 
  have h3' : c = b + d := by linarith 
  rw [h2', h3'] at h1 
  nlinarith [sq_nonneg (b - 4), sq_nonneg (d), sq_nonneg ((b - d) - b), sq_nonneg (b + d - 4), 
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
  ]