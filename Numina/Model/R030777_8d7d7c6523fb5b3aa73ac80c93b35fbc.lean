import Mathlib
open Real

theorem inequalities_4295
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    ¬(1 < (a + b) / (a + b - c) ∧ (a + b) / (a + b - c) < 2 ∧
      1 < (b + c) / (b + c - a) ∧ (b + c) / (b + c - a) < 2 ∧
      1 < (c + a) / (c + a - b) ∧ (c + a) / (c + a - b) < 2) := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩

  have pos1 : a + b - c > 0 := by
    by_contra h
    push_neg at h
    have h7 : a + b - c ≤ 0 := by linarith
    have h8 : (a + b) / (a + b - c) ≤ 1 := by
      have h9 : a + b - c ≤ 0 := h7
      have h10 : a + b - c < 0 ∨ a + b - c = 0 := by
        by_cases h11 : a + b - c < 0 
        · tauto
        · 
          have : a + b - c = 0 := by linarith
          tauto
      cases h10 with
      | inl h11 => 
        apply (div_le_iff_of_neg' h11).mpr
        nlinarith
      | inr h12 => 
        have h13 : a + b - c = 0 := by linarith
        rw [h13] at *
        norm_num at h1 ⊢
        all_goals nlinarith
    linarith [h1, h8]

  have pos2 : b + c - a > 0 := by
    by_contra h
    push_neg at h
    have h7 : b + c - a ≤ 0 := by linarith
    have h8 : (b + c) / (b + c - a) ≤ 1 := by
      have h9 : b + c - a ≤ 0 := h7
      have h10 : b + c - a < 0 ∨ b + c - a = 0 := by
        by_cases h11 : b + c - a < 0 
        · tauto
        · 
          have : b + c - a = 0 := by linarith
          tauto
      cases h10 with
      | inl h11 => 
        apply (div_le_iff_of_neg' h11).mpr
        nlinarith
      | inr h12 => 
        have h13 : b + c - a = 0 := by linarith
        rw [h13] at *
        norm_num at h3 ⊢
        all_goals nlinarith
    linarith [h3, h8]

  have pos3 : c + a - b > 0 := by
    by_contra h
    push_neg at h
    have h7 : c + a - b ≤ 0 := by linarith
    have h8 : (c + a) / (c + a - b) ≤ 1 := by
      have h9 : c + a - b ≤ 0 := h7
      have h10 : c + a - b < 0 ∨ c + a - b = 0 := by
        by_cases h11 : c + a - b < 0 
        · tauto
        · 
          have : c + a - b = 0 := by linarith
          tauto
      cases h10 with
      | inl h11 => 
        apply (div_le_iff_of_neg' h11).mpr
        nlinarith
      | inr h12 => 
        have h13 : c + a - b = 0 := by linarith
        rw [h13] at *
        norm_num at h5 ⊢
        all_goals nlinarith
    linarith [h5, h8]

  have h2' : a + b < 2 * (a + b - c) := by
    have h22 : (a + b) / (a + b - c) < 2 := h2
    apply (div_lt_iff₀ (by linarith [pos1])).mp at h22
    linarith

  have h4' : b + c < 2 * (b + c - a) := by
    have h44 : (b + c) / (b + c - a) < 2 := h4
    apply (div_lt_iff₀ (by linarith [pos2])).mp at h44
    linarith

  have h6' : c + a < 2 * (c + a - b) := by
    have h66 : (c + a) / (c + a - b) < 2 := h6
    apply (div_lt_iff₀ (by linarith [pos3])).mp at h66
    linarith

  have h7 : a + b - 2 * c > 0 := by linarith
  have h8 : b + c - 2 * a > 0 := by linarith
  have h9 : c + a - 2 * b > 0 := by linarith

  have h10 : (a + b - 2 * c) + (b + c - 2 * a) + (c + a - 2 * b) > 0 := by
    linarith [h7, h8, h9]

  have h11 : (a + b - 2 * c) + (b + c - 2 * a) + (c + a - 2 * b) = 0 := by
    ring

  linarith [h10, h11]