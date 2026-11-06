import Mathlib

theorem algebra_188353 {a b c : Fin 3 → ℝ} (h : ∃ x, a 0 + a 1 + a 2 = x ∧ b 0 + b 1 + b 2 = x ∧ c 0 + c 1 + c 2 = x ∧
    a 0 + b 0 + c 0 = x ∧ a 1 + b 1 + c 1 = x ∧ a 2 + b 2 + c 2 = x) :
    a 0 * b 0 * c 0 + a 1 * b 1 * c 1 + a 2 * b 2 * c 2 = a 0 * a 1 * a 2 + b 0 * b 1 * b 2 + c 0 * c 1 * c 2 := by
  rcases h with ⟨x, h1, h2, h3, h4, h5, h6⟩
  have hx1 : x = a 0 + a 1 + a 2 := by linarith 
  have hx2 : x = b 0 + b 1 + b 2 := by linarith
  have h_eq1 : a 0 + a 1 + a 2 = b 0 + b 1 + b 2 := by 
    linarith [h1, h2]
  have h_c0 : c 0 = a 1 + a 2 - b 0 := by
    have h7 : c 0 = x - a 0 - b 0 := by linarith
    rw [h7]
    rw [hx1]
    linarith
  have h_c1 : c 1 = a 0 + a 2 - b 1 := by
    have h8 : c 1 = x - a 1 - b 1 := by linarith
    rw [h8]
    rw [hx1]
    linarith
  have h_c2 : c 2 = a 0 + a 1 - b 2 := by
    have h9 : c 2 = x - a 2 - b 2 := by linarith
    rw [h9]
    rw [hx1]
    linarith
  have h_a2 : a 2 = b 0 + b 1 + b 2 - a 0 - a 1 := by
    linarith [h_eq1]
  simp only [h_c0, h_c1, h_c2, h_a2] at *
  ring_nf
  <;> nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (b 0 - b 1),
      sq_nonneg (a 0 + a 1 - b 0 - b 1), sq_nonneg (a 0 - b 2), sq_nonneg (a 1 - b 0)]