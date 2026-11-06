import Mathlib

theorem algebra_22104 (c : ℝ) (h : ∃a b, ∀ x y, x ^ 2 - 10 * x + y ^ 2 + 6 * y + c = 0 ↔ (x - a) ^ 2 + (y - b) ^ 2 = 1) :
    c = 33 := by
  rcases h with ⟨a, b, h_eq⟩
  have eq1 : (a + 1) ^ 2 - 10 * (a + 1) + b ^ 2 + 6 * b + c = 0 := by 
    have h11 := h_eq (a + 1) b
    norm_num at h11 ⊢ 
    nlinarith
  have eq2 : (a - 1) ^ 2 - 10 * (a - 1) + b ^ 2 + 6 * b + c = 0 := by 
    have h12 := h_eq (a - 1) b
    norm_num at h12 ⊢ 
    nlinarith
  have eq3 : a ^ 2 - 10 * a + (b + 1) ^ 2 + 6 * (b + 1) + c = 0 := by 
    have h13 := h_eq a (b + 1)
    norm_num at h13 ⊢ 
    nlinarith
  have eq4 : a ^ 2 - 10 * a + (b - 1) ^ 2 + 6 * (b - 1) + c = 0 := by 
    have h14 := h_eq a (b - 1)
    norm_num at h14 ⊢ 
    nlinarith
  have ha : a = 5 := by
    nlinarith
  have hb : b = -3 := by
    nlinarith
  rw [ha, hb] at eq1 eq2 eq3 eq4 
  nlinarith