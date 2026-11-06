import Mathlib

theorem algebra_201357 (p : ℝ) (hp : p > 0) (h1 : ∃ x, 3 * x ^ 2 - 4 * p * x + 9 = 0 ∧ x ^ 2 - 2 * p * x + 5 = 0) :
    p = 3 := by
  rcases h1 with ⟨x, h1, h2⟩
  have eq1 : 3 * x ^ 2 - 4 * p * x + 9 = 0 := h1
  have eq2 : x ^ 2 - 2 * p * x + 5 = 0 := h2

  have h3 : x ^ 2 = 2 * p * x - 5 := by linarith
  rw [h3] at eq1
  have h4 : 2 * p * x = 6 := by linarith
  have h5 : p * x = 3 := by linarith
  
  have h6 : x ^ 2 = 1 := by
    nlinarith [h3, h5]

  have h8 : x = 1 ∨ x = -1 := by
    rw [sq_eq_one_iff] at h6
    tauto
  
  cases h8 with
  | inl h9 =>
    have h10 : p = 3 := by
      rw [h9] at h5
      linarith
    linarith
  | inr h11 =>
    have h12 : p < 0 := by
      rw [h11] at h5
      nlinarith
    linarith