import Mathlib

theorem inequalities_52705 (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i)
    (h : ∃ d, ∀ i, x i ^ 2 - x i * x ((i + 1) % 5) + x ((i + 1) % 5) ^ 2 = d) :
    ∀ i, x i = x 0 := by
  rcases h with ⟨d, heq⟩
  have h1 := heq 0
  simp at h1 
  have h2 := heq 1
  simp at h2 
  have h3 := heq 2
  simp at h3 
  have h4 := heq 3
  simp at h4 
  have h5 := heq 4
  simp at h5 
  have h6 : x 0 > 0 := hx 0
  have h7 : x 1 > 0 := hx 1
  have h8 : x 2 > 0 := hx 2
  have h9 : x 3 > 0 := hx 3
  have h10 : x 4 > 0 := hx 4
  intro i 
  have eq0 : x i = x 0 := by
    have eq1 : x 0 = x 1 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4), sq_nonneg (x 4 - x 0),
        mul_pos h6 h7, mul_pos h7 h8, mul_pos h8 h9, mul_pos h9 h10, mul_pos h10 h6]
    have eq2 : x 1 = x 2 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4), sq_nonneg (x 4 - x 0),
        mul_pos h6 h7, mul_pos h7 h8, mul_pos h8 h9, mul_pos h9 h10, mul_pos h10 h6]
    have eq3 : x 2 = x 3 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4), sq_nonneg (x 4 - x 0),
        mul_pos h6 h7, mul_pos h7 h8, mul_pos h8 h9, mul_pos h9 h10, mul_pos h10 h6]
    have eq4 : x 3 = x 4 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4), sq_nonneg (x 4 - x 0),
        mul_pos h6 h7, mul_pos h7 h8, mul_pos h8 h9, mul_pos h9 h10, mul_pos h10 h6]
    have eq5 : x 4 = x 0 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4), sq_nonneg (x 4 - x 0),
        mul_pos h6 h7, mul_pos h7 h8, mul_pos h8 h9, mul_pos h9 h10, mul_pos h10 h6]
    have h11 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      fin_cases i <;> simp 
    rcases h11 with (r | r | r | r | r)
    · 
      rw [r]
    · 
      rw [r]
      linarith [eq1]
    · 
      rw [r]
      linarith [eq2, eq1]
    · 
      rw [r]
      linarith [eq3, eq2, eq1]
    · 
      rw [r]
      linarith [eq4, eq3, eq2, eq1]
  exact eq0