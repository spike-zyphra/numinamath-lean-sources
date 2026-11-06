import Mathlib

theorem algebra_246560 {a b c d : ℕ} (h : (a + b) ^ 2 + a = (c + d) ^ 2 + c) :
    a = c ∧ b = d := by 
  have h1 : a + b ≥ c + d := by
    by_contra h2
    push_neg at h2
    have h3 : (a + b) ^ 2 < (c + d) ^ 2 := by
      have : c + d > a + b := by linarith
      have h4 : (c + d) ^ 2 > (a + b) ^ 2 := by nlinarith
      linarith
    have h5 : (a + b) ^ 2 + a < (c + d) ^ 2 + c := by
      linarith [h3, show a ≤ c by nlinarith]
    linarith
  have h2 : a + b ≤ c + d := by
    by_contra h3
    push_neg at h3
    have h3 : (a + b) ^ 2 > (c + d) ^ 2 := by
      have : a + b > c + d := by linarith
      have h4 : (a + b) ^ 2 > (c + d) ^ 2 := by nlinarith
      linarith
    have h5 : (a + b) ^ 2 + a > (c + d) ^ 2 + c := by
      linarith [h3, show c ≤ a by nlinarith]
    linarith
  have h_eq1 : a + b = c + d := by
    linarith
  have h3 : a = c := by
    have h4 : (a + b) ^ 2 + a = (c + d) ^ 2 + c := h
    rw [show (a + b) = c + d by linarith] at h4
    nlinarith 
  have h4 : b = d := by
    omega
  exact ⟨h3, h4⟩