import Mathlib

theorem algebra_186397 {a b c d : ℝ} (h₀ : ∃ r, b = a * r ∧ c = b * r ∧ d = c * r)
    (h₁ : a + d = -49) (h₂ : b + c = 14) :
    (a = 7 ∧ b = -14 ∧ c = 28 ∧ d = -56) ∨ (a = -56 ∧ b = 28 ∧ c = -14 ∧ d = 7) := by 
  rcases h₀ with ⟨r, h₃, h₄, h₅⟩
  have eq1 : c = a * r ^ 2 := by 
    have eq1 : c = b * r := h₄ 
    rw [eq1] 
    rw [h₃] 
    <;> ring 
  have eq2 : d = a * r ^ 3 := by 
    have eq2 : d = c * r := h₅ 
    rw [eq2] 
    rw [eq1] 
    <;> ring 
  rw [eq2] at h₁ 
  have eq3 : b = a * r := h₃ 
  rw [eq3] at h₂ 
  rw [show c = a * r ^ 2 by linarith [eq1]] at h₂ 
  have h_eq1 : a * (1 + r ^ 3) = -49 := by 
    nlinarith 
  have h_eq2 : a * r * (1 + r) = 14 := by 
    nlinarith 
  have h_eq3 : 2 * r ^ 2 + 5 * r + 2 = 0 := by
    have h_eq4 : 1 + r ^ 3 = (1 + r) * (1 - r + r ^ 2) := by 
      ring
    rw [h_eq4] at h_eq1 
    by_cases hr1 : r = -1 
    · -- r = -1 
      rw [hr1] at h_eq2 
      nlinarith 
    · -- r ≠ -1 
      have h_eq7 : r ≠ -1 := hr1
      by_cases hr0 : r = 0 
      · -- r = 0
        rw [hr0] at h_eq2 
        nlinarith 
      · -- r ≠ 0 
        have h_eq8 : r ≠ 0 := hr0
        have h_eq9 : a * (1 + r) = 14 / r := by 
          have h_eq10 : r ≠ 0 := h_eq8 
          field_simp [h_eq10] 
          <;> nlinarith 
        have h_eq6 : a * (1 + r) * (1 - r + r ^ 2) = -49 := by
          nlinarith 
        rw [show a * (1 + r) = 14 / r by 
          have h_eq10 : r ≠ 0 := h_eq8 
          field_simp [h_eq10] 
          <;> nlinarith 
        ] at h_eq6 
        field_simp [show r ≠ 0 by exact h_eq8] at h_eq6 
        nlinarith 
  have h_eq5 : (r + 1 / 2) * (r + 2) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.1 h_eq5) with h_eq6 h_eq7 
  · -- r = -1/2 
    have hr1 : r = -1 / 2 := by 
      linarith 
    have ha1 : a = -56 := by
      rw [hr1] at h_eq2 
      nlinarith 
    have hb1 : b = 28 := by 
      rw [h₃, ha1, hr1] 
      norm_num 
    have hc1 : c = -14 := by 
      rw [eq1, ha1, hr1] 
      norm_num 
    have hd1 : d = 7 := by 
      rw [eq2, ha1, hr1] 
      norm_num 
    right 
    constructor 
    · -- a = -56 
      linarith 
    constructor 
    · -- b = 28 
      linarith 
    constructor 
    · -- c = -14 
      linarith 
    · -- d = 7 
      linarith 
  · -- r = -2 
    have hr2 : r = -2 := by 
      linarith 
    have ha2 : a = 7 := by 
      rw [hr2] at h_eq2 
      nlinarith 
    have hb2 : b = -14 := by 
      rw [h₃, ha2, hr2] 
      norm_num 
    have hc2 : c = 28 := by 
      rw [eq1, ha2, hr2] 
      norm_num 
    have hd2 : d = -56 := by 
      rw [eq2, ha2, hr2] 
      norm_num 
    left 
    constructor 
    · -- a = 7 
      linarith 
    constructor 
    · -- b = -14 
      linarith 
    constructor 
    · -- c = 28 
      linarith 
    · -- d = -56 
      linarith