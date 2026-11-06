import Mathlib

open Real Set
open scoped Real

theorem calculus_22899 (x : ℝ) (hx : x ∈ Icc 0 (2 * π)) (hcos: cos x ≠ 0): tan x = sin x ↔ x = 0 ∨ x = π ∨ x = 2 * π := by
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Assume tan x = sin x 
    intro h
    have htan : tan x = sin x / cos x := by
      rw [tan_eq_sin_div_cos]
    rw [htan] at h
    have h1 : sin x = sin x * cos x := by 
      have hcos' : cos x ≠ 0 := hcos
      field_simp [hcos'] at h
      nlinarith [h]
    have h2 : sin x * (cos x - 1) = 0 := by 
      linarith [h1]
    cases (mul_eq_zero.mp h2) with 
    | inl h3 =>
      have h5 : sin x = 0 := h3
      have h6 : x = 0 ∨ x = π ∨ x = 2 * π := by
        have h7 : sin x = 0 := h5
        have h8 : x ≥ 0 := hx1
        have h9 : x ≤ 2 * π := hx2
        have h30 : x = 0 ∨ x = π ∨ x = 2 * π := by
          have h31 : sin x = 0 := h7
          have h40 : ∃ k : ℤ, x = k * Real.pi := by
            have h41 : sin x = 0 := h31
            have h42 : ∃ k : ℤ, x = k * Real.pi := by
              rw [sin_eq_zero_iff] at h41
              rcases h41 with ⟨k, hk⟩
              have : ∃ k : ℤ, x = k * Real.pi := ⟨k, by nlinarith⟩
              exact this
            exact h42
          rcases h40 with ⟨k, hk⟩
          have h47 : k ≥ 0 := by
            by_contra h
            push_neg at h
            have h48 : k < 0 := by omega 
            have h49 : (k : ℝ) < (0 : ℝ) := by exact_mod_cast h48 
            nlinarith [Real.pi_pos]
          have h48 : k ≤ 2 := by
            by_contra h
            push_neg at h
            have h49 : k > 2 := by omega 
            have h50 : (k : ℝ) > (2 : ℝ) := by exact_mod_cast h49 
            nlinarith [Real.pi_pos]
          have : k = 0 ∨ k = 1 ∨ k = 2 := by 
            omega
          rcases this with (r | r | r)
          · -- k = 0 
            have h52 : (k : ℝ) = (0 : ℝ) := by exact_mod_cast r 
            rw [h52] at hk 
            left 
            nlinarith 
          · -- k = 1 
            have h52 : (k : ℝ) = (1 : ℝ) := by exact_mod_cast r 
            rw [h52] at hk 
            right 
            left 
            nlinarith 
          · -- k = 2 
            have h52 : (k : ℝ) = (2 : ℝ) := by exact_mod_cast r 
            rw [h52] at hk 
            right 
            right 
            nlinarith 
        exact h30 
      tauto 
    | inr h4 =>
      have h4' : cos x = 1 := by linarith 
      have h5 : x = 0 ∨ x = 2 * π := by 
        have h6 : cos x = 1 := h4' 
        have h7 : x ≥ 0 := hx1 
        have h8 : x ≤ 2 * π := hx2 
        have h76 : x = 0 ∨ x = 2 * π := by 
          have h46 : cos x = 1 := h6 
          have h47 : ∃ k : ℤ, x = 2 * k * Real.pi := by 
            have h48 : cos x = 1 := h46 
            have h49 : ∃ k : ℤ, x = 2 * k * Real.pi := by 
              rw [cos_eq_one_iff] at h48 
              rcases h48 with ⟨k, hk⟩ 
              have : x = 2 * (k : ℝ) * Real.pi := by linarith 
              have : (x : ℝ) = 2 * (k : ℝ) * Real.pi := by linarith 
              have : ∃ k : ℤ, x = 2 * k * Real.pi := by 
                use k 
                all_goals 
                  norm_num at this ⊢ 
                  <;> nlinarith 
              exact this 
            exact h49 
          rcases h47 with ⟨k, hk⟩ 
          have h48 : k ≥ 0 := by 
            by_contra h
            push_neg at h 
            have h49 : k < 0 := by omega 
            have h50 : (k : ℝ) < (0 : ℝ) := by exact_mod_cast h49 
            nlinarith [Real.pi_pos] 
          have h49 : k ≤ 1 := by 
            by_contra h 
            push_neg at h 
            have h50 : k > 1 := by omega 
            have h51 : (k : ℝ) > (1 : ℝ) := by exact_mod_cast h50 
            nlinarith [Real.pi_pos] 
          have : k = 0 ∨ k = 1 := by 
            omega 
          rcases this with (r | r) 
          · -- k = 0 
            have h52 : (k : ℝ) = (0 : ℝ) := by exact_mod_cast r 
            rw [h52] at hk 
            left 
            nlinarith 
          · -- k = 1 
            have h52 : (k : ℝ) = (1 : ℝ) := by exact_mod_cast r 
            rw [h52] at hk 
            right 
            nlinarith 
        exact h76 
      cases h5 with 
      | inl h5 =>
        tauto 
      | inr h5 =>
        tauto 
  · -- Assume x = 0 ∨ x = π ∨ x = 2 * π 
    rintro (h | h | h)
    · -- x = 0 
      rw [h] 
      have htan0 : tan (0 : ℝ) = 0 := by 
        rw [tan_eq_sin_div_cos] 
        simp 
      simp [htan0]
    · -- x = π 
      rw [h] 
      have htanpi : tan π = 0 := by 
        rw [tan_eq_sin_div_cos]
        simp [sin_pi, cos_pi]
      simp [htanpi, sin_pi]
    · -- x = 2 * π 
      rw [h] 
      have htan2pi : tan (2 * π) = 0 := by 
        rw [tan_eq_sin_div_cos]
        simp [sin_two_pi, cos_two_pi]
      simp [htan2pi, sin_two_pi]