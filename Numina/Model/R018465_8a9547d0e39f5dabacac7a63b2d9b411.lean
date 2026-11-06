import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12952 {c : ℝ} :
  (∃! x : ℝ, x^2 + x - 20 = 0 ∧ (x^2 - x + c) ≠ 0) ↔ c = -12 ∨ c = -30 := by
  constructor
  · -- Assume there is a unique vertical asymptote, prove c = -12 ∨ c = -30
    intro h
    rcases h with ⟨x, ⟨h1, h2⟩, h3⟩
    have h4 : x ^ 2 + x - 20 = 0 := h1
    have h5 : x ^ 2 - x + c ≠ 0 := h2

    have h6 : x = -5 ∨ x = 4 := by
      have : (x + 5) * (x - 4) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 this) with h7 h8
      · -- Case x + 5 = 0
        left
        linarith
      · -- Case x - 4 = 0
        right
        linarith

    cases h6 with
    | inl hx =>
      -- x = -5
      have hx1 : x = -5 := hx
      have h7 : (4 : ℝ) ^ 2 + (4 : ℝ) - 20 = 0 := by norm_num
      have h8 : (4 : ℝ) ^ 2 + (4 : ℝ) - 20 = 0 ∧ (4 : ℝ) ^ 2 - (4 : ℝ) + c ≠ 0 → (4 : ℝ) = x := by
        apply h3
      -- Assume that y = 4 is a solution, then 4 = x.
      -- But x = -5, contradiction unless 4 = -5, which is impossible.
      -- So it must be that (4 : ℝ) ^ 2 - (4 : ℝ) + c = 0.
      -- i.e., 16 - 4 + c = 0 ⇒ 12 + c = 0 ⇒ c = -12.
      by_cases h9 : (4 : ℝ) ^ 2 - (4 : ℝ) + c = 0
      · -- Assume (4 : ℝ) ^ 2 - (4 : ℝ) + c = 0
        -- From h9, we have 16 - 4 + c = 0 ⇒ 12 + c = 0 ⇒ c = -12
        have hc : c = -12 := by linarith
        left
        nlinarith
      · -- Assume (4 : ℝ) ^ 2 - (4 : ℝ) + c ≠ 0
        have h9' : (4 : ℝ) ^ 2 - (4 : ℝ) + c ≠ 0 := by
          simpa using h9
        have h10 : (4 : ℝ) ^ 2 + (4 : ℝ) - 20 = 0 := by norm_num
        have h11 := h8 ⟨by norm_num, h9'⟩
        nlinarith [hx1, h11]
    | inr hx =>
      -- x = 4
      have hx1 : x = 4 := hx
      have h7 : (-5 : ℝ) ^ 2 + (-5 : ℝ) - 20 = 0 := by norm_num
      have h8 : (-5 : ℝ) ^ 2 + (-5 : ℝ) - 20 = 0 ∧ (-5 : ℝ) ^ 2 - (-5 : ℝ) + c ≠ 0 → (-5 : ℝ) = x := by
        apply h3
      by_cases h9 : (-5 : ℝ) ^ 2 - (-5 : ℝ) + c = 0
      · -- Assume (-5 : ℝ) ^ 2 - (-5 : ℝ) + c = 0
        -- From h9, we have 25 + 5 + c = 0 ⇒ 30 + c = 0 ⇒ c = -30
        have hc : c = -30 := by linarith
        right
        nlinarith
      · -- Assume (-5 : ℝ) ^ 2 - (-5 : ℝ) + c ≠ 0
        have h9' : (-5 : ℝ) ^ 2 - (-5 : ℝ) + c ≠ 0 := by
          simpa using h9
        have h10 : (-5 : ℝ) ^ 2 + (-5 : ℝ) - 20 = 0 := by norm_num
        have h11 := h8 ⟨by norm_num, h9'⟩
        nlinarith [hx1, h11]
  intro h
  rcases h with (h | h)
  · -- Assume c = -12
    use -5
    constructor
    · -- Show that -5 is indeed a solution
      constructor
      · -- Show that (-5)^2 + (-5) - 20 = 0
        norm_num
      · -- Show that (-5)^2 - (-5) + c ≠ 0
        rw [h]
        norm_num
    · -- Show that -5 is unique
      intro y h3
      rcases h3 with ⟨hy1, hy2⟩
      have h4 : y ^ 2 + y - 20 = 0 := hy1
      have h5 : y ^ 2 - y + c ≠ 0 := hy2

      have h6 : y = -5 ∨ y = 4 := by
        have : (y + 5) * (y - 4) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 this) with h7 h8
        · -- Case y + 5 = 0
          left
          linarith
        · -- Case y - 4 = 0
          right
          linarith

      cases h6 with
      | inl hy =>
        linarith
      | inr hy =>
        -- y = 4 leads to a contradiction since the numerator would be 0
        have h9 : c = -12 := by linarith [h]
        have h10 : y ^ 2 - y + c = 0 := by
          rw [show c = -12 from h]
          nlinarith [show y = (4 : ℝ) by linarith]
        have h11 : y ^ 2 - y + c ≠ 0 := h5
        contradiction
  · -- Assume c = -30
    use 4
    constructor
    · -- Show that 4 is indeed a solution
      constructor
      · -- Show that (4)^2 + (4) - 20 = 0
        norm_num
      · -- Show that (4)^2 - (4) + c ≠ 0
        rw [h]
        norm_num
    · -- Show that 4 is unique
      intro y h3
      rcases h3 with ⟨hy1, hy2⟩
      have h4 : y ^ 2 + y - 20 = 0 := hy1
      have h5 : y ^ 2 - y + c ≠ 0 := hy2

      have h6 : y = -5 ∨ y = 4 := by
        have : (y + 5) * (y - 4) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 this) with h7 h8
        · -- Case y + 5 = 0
          left
          linarith
        · -- Case y - 4 = 0
          right
          linarith

      cases h6 with
      | inl hy =>
        -- y = -5 leads to a contradiction since the numerator would be 0
        have h9 : c = -30 := by linarith [h]
        have h10 : y ^ 2 - y + c = 0 := by
          rw [show c = -30 from h]
          nlinarith [show y = (-5 : ℝ) by linarith]
        have h11 : y ^ 2 - y + c ≠ 0 := h5
        contradiction
      | inr hy =>
        linarith