import Mathlib

theorem algebra_223261 {f g : ℝ → ℝ} (hf : ∃ b : ℝ, b ≠ 0 ∧ f = fun x => x ^ 2 + b * x + 8)
    (hg : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ f x1 = 0 ∧ f x2 = 0 ∧ g = fun x => (x - (x1 + 1 / x2)) * (x - (x2 + 1 / x1)))
    (h1 : g 1 = f 1) : g 1 = -8 := by
  rcases hf with ⟨b, hb_ne_zero, hf_eq⟩
  rcases hg with ⟨x1, x2, hx12, hf1, hf2, hg_eq⟩
  have h_eq1 : x1 ^ 2 + b * x1 + 8 = 0 := by 
    rw [hf_eq] at hf1
    simpa using hf1
  have h_eq2 : x2 ^ 2 + b * x2 + 8 = 0 := by 
    rw [hf_eq] at hf2
    simpa using hf2
  have h_eq3 : x1 + x2 = -b := by
    have h_sub : (x1 - x2) * (x1 + x2 + b) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h_sub) with
    | inl h => 
      exfalso
      apply hx12
      linarith
    | inr h => 
      linarith
  have h_eq4 : x1 * x2 = 8 := by
    have h_add : (x1 ^ 2 + x2 ^ 2) + b * (x1 + x2) + 16 = 0 := by 
      nlinarith
    have h_eq5 : (x1 ^ 2 + x2 ^ 2) = (x1 + x2)^2 - 2 * (x1 * x2) := by
      nlinarith [sq_nonneg (x1 - x2)]
    rw [h_eq3] at h_add
    rw [h_eq5] at h_add
    nlinarith
  have h_eq5 : g 1 = (1 - (x1 + 1 / x2)) * (1 - (x2 + 1 / x1)) := by
    rw [hg_eq]
  have h_eq7 : x1 ≠ 0 := by
    by_contra h
    rw [h] at h_eq4
    nlinarith
  have h_eq8 : x2 ≠ 0 := by
    by_contra h
    rw [h] at h_eq4
    nlinarith
  have h_eq10 : b = -17 := by
    have h_eq6 : g 1 = f 1 := h1
    rw [h_eq5, show f 1 = 1 ^ 2 + b * 1 + 8 by simp [hf_eq]] at h_eq6
    field_simp [show x1 ≠ 0 by exact h_eq7, show x2 ≠ 0 by exact h_eq8] at h_eq6
    nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by
      intro h'
      apply hx12
      linarith
    ), h_eq3, h_eq4, sq_nonneg (x1 - x2), sq_nonneg (x1 + x2)]
  have h_eq3' : (1 - (x1 + 1 / x2)) * (1 - (x2 + 1 / x1)) = -8 := by
    have eq1 : (1 - (x1 + 1 / x2)) * (1 - (x2 + 1 / x1)) = 1 ^ 2 + b * 1 + 8 := by
      have eq7 : (1 - (x1 + 1 / x2)) * (1 - (x2 + 1 / x1)) = 1 ^ 2 + b * 1 + 8 := by
        have h_eq6 : g 1 = f 1 := h1
        rw [h_eq5, show f 1 = 1 ^ 2 + b * 1 + 8 by simp [hf_eq]] at h_eq6
        linarith
      linarith [eq7]
    rw [show b = -17 by linarith [h_eq10]] at eq1
    norm_num at eq1 ⊢
    linarith
  rw [h_eq5]
  exact h_eq3'