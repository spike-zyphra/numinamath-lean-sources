import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13389 {x : ℝ} (hx : x ≠ 0) :
    (2 * x - 7) * (x - 3) / x ≥ 0 ↔ x ∈ Ioc 0 3 ∪ Ici (7 / 2) := by
  constructor
  · -- Let 's proving if (2 * x - 7) * (x - 3) / x ≥ 0 then x ∈ (0, 3] ∪ [7/2, +∞).
    intro h
    have h1 : (2 * x - 7) * (x - 3) / x ≥ 0 := h
    have h2 : x ≠ 0 := hx
    by_cases h11 : x > 0 
    · -- First, consider the case where x > 0.  
      have h4 : x > 0 := h11 
      have h6 : (2 * x - 7) * (x - 3) ≥ 0 := by
        have h7 : (2 * x - 7) * (x - 3) / x ≥ 0 := h1 
        apply (div_nonneg_iff).mp at h7 
        cases h7 with 
        | inl h0 =>
          nlinarith 
        | inr h0 =>
          nlinarith 
      by_cases h7 : x ≤ 3
      · -- First case : 0 < x ≤ 3. Then x ∈ (0, 3] subset as required.
        left
        exact ⟨by linarith, h7⟩
      · -- Second case : x > 3 (to ∞), perhaps [(7/2) to ∞).
        have h8 : x ≥ 7 / 2 := by nlinarith
        right
        exact h8 
    · -- x ≤ 0. (x < 0)
      have h11 : x < 0 := by 
        by_contra h
        push_neg at h 
        have : x ≥ 0 := by linarith 
        have : x = 0 := by linarith 
        tauto 
      have h4 : x < 0 := h11 
      have h5 : (2 * x - 7) * (x - 3) ≤ 0 := by 
        have h6 : (2 * x - 7) * (x - 3) / x ≥ 0 := h1 
        apply (div_nonneg_iff).mp at h6 
        cases h6 with 
        | inl h0 => 
          nlinarith 
        | inr h0 => 
          nlinarith 
      exfalso 
      nlinarith 
  · -- π → h  with h given h3 := if direction mistake `.exact` satisfied.
    intro h
    rcases h with (h | h)
    · -- First case (x ∈ (0, 3])
      rcases h with ⟨h1, h2⟩ 
      have h4 : x > 0 := h1 
      have h5 : x ≤ 3 := h2 
      have h7 : (2 * x - 7) * (x - 3) ≥ 0 := by nlinarith 
      have h3 : (2 * x - 7) * (x - 3) / x ≥ 0 := by
        apply div_nonneg 
        linarith 
        linarith 
      linarith
    · -- Second case (x ∈ [7/2, ∞))
      have h4 : x ≥ 7 / 2 := h 
      have h6 : (2 * x - 7) * (x - 3) ≥ 0 := by nlinarith 
      have h3 : (2 * x - 7) * (x - 3) / x ≥ 0 := by
        apply div_nonneg 
        linarith 
        linarith 
      linarith