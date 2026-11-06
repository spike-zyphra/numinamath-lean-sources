import Mathlib

theorem algebra_10582 {N : ℕ} (hN : N ≥ 6) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : (N-3) * (a+b+c)/(N:ℝ) = N * (a+b+c)/(N:ℝ) * (1 - 35 / 100)) (h2 : (N-6) * (a+c)/(N:ℝ) = (N-3) * (a+b+c)/(N:ℝ) * (1 - 5 / 13)) : N = 10 := by

  have h3 : (N:ℝ) > 0 := by
    have hN' : (N:ℝ) ≥ (6:ℝ) := by exact_mod_cast hN
    linarith
  have h4 : (N - 3) * (a + b + c) = (N:ℝ) * (a + b + c) * (1 - 35 / 100) := by 
    have hN' : (N:ℝ) > 0 := h3
    field_simp at h1 ⊢
    ring_nf at h1 ⊢
    <;> nlinarith
  
  have h6 : (N - 3) * (a + b + c) = (N:ℝ) * (a + b + c) * (65 / 100) := by 
    linarith [h4]

  have h7 : (N - 6) * (a + c) = (N - 3) * (a + b + c) * (1 - 5 / 13) := by 
    have hN' : (N:ℝ) > 0 := h3
    field_simp at h2 ⊢
    ring_nf at h2 ⊢
    <;> nlinarith
  have h8 : (N - 6) * (a + c) = (N - 3) * (a + b + c) * (8 / 13) := by 
    nlinarith [h7]
  have h9 : (N:ℝ) > 0 := h3
  have h10 : a + b + c > 0 := by linarith
  have h11 : a + c > 0 := by linarith
  have eq1 : (N:ℝ) = 10 := by
    nlinarith [sq_nonneg ((N:ℝ) - 10), sq_nonneg (a - c), sq_pos_of_pos ha, sq_pos_of_pos hc, sq_nonneg (b)]
  have h12 : N = 10 := by
    have h13 : (N:ℝ) = 10 := eq1
    have h14 : (N:ℕ) = 10 := by
      exact_mod_cast h13
    exact h14
  exact h12