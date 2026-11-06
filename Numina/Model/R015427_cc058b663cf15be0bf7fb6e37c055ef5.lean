import Mathlib

theorem algebra_234039 (u v w : ℝ) (h₀ : u + v * w = 20) (h₁ : v + w * u = 20) (h₂ : w + u * v = 20) :
    (u = 4 ∧ v = 4 ∧ w = 4) ∨ (u = -5 ∧ v = -5 ∧ w = -5) ∨ (u = 1 ∧ v = 1 ∧ w = 19) ∨
    (u = 1 ∧ v = 19 ∧ w = 1) ∨ (u = 19 ∧ v = 1 ∧ w = 1) := by

  have eq1 : (u - v) * (1 - w) = 0 := by 
    nlinarith 
  have eq2 : (v - w) * (1 - u) = 0 := by 
    nlinarith 
  have eq3 : (w - u) * (1 - v) = 0 := by 
    nlinarith 
  cases (mul_eq_zero.mp eq1) with
  | inl h3 =>
    have h3 : u = v := by linarith 
    have eq2' : (u - w) * (1 - u) = 0 := by
      rw [show v = u by linarith [h3]] at eq2
      nlinarith 
    cases (mul_eq_zero.mp eq2') with
    | inl h4 =>
      have h4 : u = w := by linarith 
      have h5 : u = v := by linarith [h3] 
      have h6 : u ^ 2 + u - 20 = 0 := by
        have h7 : u + u * u = 20 := by
          have h8 : u + v * w = 20 := h₀
          rw [show v = u by linarith [h3], show w = u by linarith [h4]] at h8
          linarith 
        nlinarith 
      have h7 : (u - 4) * (u + 5) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.mp h7) with
      | inl h8 =>
        have h8 : u = 4 := by linarith 
        have h9 : v = 4 := by linarith [h3, h8] 
        have h10 : w = 4 := by linarith [h4, h8] 
        left 
        exact ⟨h8, h9, h10⟩ 
      | inr h8 =>
        have h8 : u = -5 := by linarith 
        have h9 : v = -5 := by linarith [h3, h8] 
        have h10 : w = -5 := by linarith [h4, h8] 
        right 
        left 
        exact ⟨h8, h9, h10⟩ 
    | inr h4 =>
      have h4 : u = 1 := by linarith 
      have h5 : v = 1 := by linarith [h3, h4] 
      have h6 : w = 19 := by 
        rw [show u = 1 by linarith [h4], show v = 1 by linarith [h5]] at h₂ 
        nlinarith 
      simp [h4, h5, h6] 
  | inr h3 =>
    have h3 : w = 1 := by linarith 
    have eq2' : (v - 1) * (1 - u) = 0 := by
      rw [show w = 1 by linarith [h3]] at eq2
      nlinarith 
    cases (mul_eq_zero.mp eq2') with
    | inl h4 =>
      have h4 : v = 1 := by linarith 
      have h5 : u = 19 := by 
        rw [show v = 1 by linarith [h4], show w = 1 by linarith [h3]] at h₀ 
        nlinarith 
      simp [h5, h4, h3] 
    | inr h4 =>
      have h4 : u = 1 := by linarith 
      have h5 : v = 19 := by 
        rw [show u = 1 by linarith [h4], show w = 1 by linarith [h3]] at h₀ 
        nlinarith 
      simp [h4, h5, h3]