import Mathlib

theorem algebra_235550 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h1 : a + b = a * b) (h2 : a * b = a / b) :
    a = 1 / 2 ∧ b = -1 := by
  have h3 : a * b ^ 2 = a := by 
    have eq1 : a * b = a / b := h2
    have eq2 : a * b * b = a := by
      field_simp [hb] at eq1 ⊢
      all_goals
        nlinarith [eq1]
    nlinarith
  have h4 : a * (b ^ 2 - 1) = 0 := by 
    nlinarith [h3]
  have h5 : b ^ 2 - 1 = 0 := by 
    apply_fun (λ x => x / a) at h4
    field_simp [ha] at h4 ⊢
    all_goals nlinarith
  have h6 : b ^ 2 = 1 := by 
    linarith 
  have h7 : b = 1 ∨ b = -1 := by
    rw [sq_eq_one_iff] at h6
    exact h6
  cases h7 with
  | inl hb1 =>
    -- If b = 1, then from a + b = a * b we get a + 1 = a, which is a contradiction
    have hb1' : b = 1 := hb1
    rw [hb1'] at h1
    have h8 : a + 1 = a := by
      nlinarith 
    have h9 : (1 : ℝ) = 0 := by 
      linarith 
    linarith 
  | inr hb2 =>
    -- If b = -1, then from a + b = a * b we get a - 1 = -a, so a = 1/2
    have hb2' : b = -1 := hb2
    rw [hb2'] at h1
    have h9 : a = 1 / 2 := by 
      nlinarith 
    constructor 
    · exact h9 
    · exact hb2'