import Mathlib
open Nat Real Finset

/-Three rational numbers $a$, $b$, $c$, their product is negative, and their sum is positive. When $x=\frac{|a|}{a}+\frac{|b|}{b}+\frac{|c|}{c}$, the value of the algebraic expression $x^{17}-17x+8$ is 
___ ___ .-/
theorem number_theory_600012 (a b c : ℚ) (h₀ : a * b * c < 0) (h₁ : a + b + c > 0)
    (x : ℝ) (hx : x = abs a / a + abs b / b + abs c / c) :
    x ^ 17 - 17 * x + 8 = -8 := by
  -- Prove $a, b, c ≠ 0$.
  have h_nonzero : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
    have h₁: a ≠ 0 := by
      intro ha
      rw [ha] at h₀
      simp at h₀
    have h₂: b ≠ 0 := by
      intro hb
      rw [hb] at h₀
      simp at h₀
    have h₃: c ≠ 0 := by
      intro hc
      rw [hc] at h₀
      simp at h₀
    exact ⟨h₁, h₂, h₃⟩
  -- Prove one negative, two positive.
  have h_signs : (a < 0 ∧ b > 0 ∧ c > 0) ∨ (a > 0 ∧ b < 0 ∧ c > 0) ∨ (a > 0 ∧ b > 0 ∧ c < 0) := by
      have ha : a < 0 ∨ a > 0 := by simp [h_nonzero.1]
      have hb : b < 0 ∨ b > 0 := by simp [h_nonzero.2.1]
      have hc : c < 0 ∨ c > 0 := by simp [h_nonzero.2.2]
      cases ha with
      | inl ha_neg =>
        cases hb with
        | inl hb_neg =>
          cases hc with
          | inl hc_neg =>
            have : a + b + c < 0 := by
              have : a < 0 := ha_neg
              have : b < 0 := hb_neg
              have : c < 0 := hc_neg
              linarith
            linarith [this, h₁]
          | inr hc_pos =>
            have : a * b * c > 0 := by
              have : a < 0 := ha_neg
              have : b < 0 := hb_neg
              have : c > 0 := hc_pos
              have : a * b > 0 := by nlinarith
              nlinarith
            linarith [this, h₀]
        | inr hb_pos =>
          cases hc with
          | inl hc_neg =>
            have : a * b * c > 0 := by
              have : a < 0 := ha_neg
              have : b > 0 := hb_pos
              have : c < 0 := hc_neg
              have : b * c < 0 := by nlinarith
              nlinarith
            linarith [this, h₀]
          | inr hc_pos => exact Or.inl ⟨ha_neg, hb_pos, hc_pos⟩
      | inr ha_pos =>
        cases hb with
        | inl hb_neg =>
          cases hc with
          | inl hc_neg =>
            have : a * b * c > 0 := by
              have : a > 0 := ha_pos
              have : b < 0 := hb_neg
              have : c < 0 := hc_neg
              have : b * c > 0 := by nlinarith
              nlinarith
            linarith [this, h₀]
          | inr hc_pos => exact Or.inr (Or.inl ⟨ha_pos, hb_neg, hc_pos⟩)
        | inr hb_pos =>
          cases hc with
          | inl hc_neg => exact Or.inr (Or.inr ⟨ha_pos, hb_pos, hc_neg⟩)
          | inr hc_pos =>
            have : a * b * c > 0 := by
              have : a > 0 := ha_pos
              have : b > 0 := hb_pos
              have : c > 0 := hc_pos
              have : b * c > 0 := by nlinarith
              nlinarith
            linarith [this, h₀]
  -- Compute $x = 1$.
  have h_x_eq_1 : x = 1 := by
    rw [hx]
    cases h_signs with
    | inl h =>
      have h_a_neg : abs a / a = -1 := by
        have : a < 0 := h.1
        rw [abs_of_neg this]
        field_simp [h_nonzero.1]
      have h_b_pos : abs b / b = 1 := by
        have : b > 0 := h.2.1
        rw [abs_of_pos this]
        field_simp [h_nonzero.2.1]
      have h_c_pos : abs c / c = 1 := by
        have : c > 0 := h.2.2
        rw [abs_of_pos this]
        field_simp [h_nonzero.2.2]
      have h_sum : (abs a / a + abs b / b + abs c / c : ℝ) = 1 := by
          norm_cast
          rw [h_a_neg, h_b_pos, h_c_pos]
          norm_num
      exact h_sum
    | inr h_cases =>
      cases h_cases with
      | inl h =>
        have h_a_pos : abs a / a = 1 := by
          have : a > 0 := h.1
          rw [abs_of_pos this]
          field_simp [h_nonzero.1]
        have h_b_neg : abs b / b = -1 := by
          have : b < 0 := h.2.1
          rw [abs_of_neg this]
          field_simp [h_nonzero.2.1]
        have h_c_pos : abs c / c = 1 := by
          have : c > 0 := h.2.2
          rw [abs_of_pos this]
          field_simp [h_nonzero.2.2]
        have h_sum : (abs a / a + abs b / b + abs c / c : ℝ) = 1 := by
          norm_cast
          rw [h_a_pos, h_b_neg, h_c_pos]
          norm_num
        exact h_sum
      | inr h =>
        have h_a_pos : abs a / a = 1 := by
          have : a > 0 := h.1
          rw [abs_of_pos this]
          field_simp [h_nonzero.1]
        have h_b_pos : abs b / b = 1 := by
          have : b > 0 := h.2.1
          rw [abs_of_pos this]
          field_simp [h_nonzero.2.1]
        have h_c_neg : abs c / c = -1 := by
          have : c < 0 := h.2.2
          rw [abs_of_neg this]
          field_simp [h_nonzero.2.2]
        have h_sum : (abs a / a + abs b / b + abs c / c : ℝ) = 1 := by
          norm_cast
          rw [h_a_pos, h_b_pos, h_c_neg]
          norm_num
        exact h_sum
  -- Substitute $x = 1$ into the expression.
  have h_result : x ^ 17 - 17 * x + 8 = -8 := by
    rw [h_x_eq_1]
    simp
    norm_num
  exact h_result
