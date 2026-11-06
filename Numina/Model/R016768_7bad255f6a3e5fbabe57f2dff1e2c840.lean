import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_306927 {f : ℝ → ℝ} (hf : f = λ x => -11 / (x + 1) + 3) :
    Function.Injective f ∧ ∀ x ∈ Ioo (-1) 10, f x < 2 := by
  constructor
  · -- Show that f is injective
    intro a b h_eq
    rw [hf] at h_eq
    -- h_eq : -11 / (a + 1) + 3 = -11 / (b + 1) + 3
    have h_eq1 : -11 / (a + 1) + 3 = -11 / (b + 1) + 3 := by 
      simpa using h_eq
    have h_eq2 : -11 / (a + 1) = -11 / (b + 1) := by 
      linarith
    by_cases h_eq3 : a + 1 = 0
    · -- Case where a + 1 = 0, so a = -1
      have h1 : b + 1 = 0 := by
        by_contra h2
        have h3 : -11 / (b + 1) ≠ 0 := by
          have h4 : b + 1 ≠ 0 := h2
          field_simp [h4]
        have eq1 : -11 / (b + 1) = 0 := by
          have eq2 : -11 / (a + 1) = 0 := by
            rw [show a + 1 = (0 : ℝ) by linarith]
            norm_num
          linarith [h_eq2, eq2]
        contradiction
      have h2 : a = -1 := by 
        linarith
      have h3 : b = -1 := by 
        linarith
      linarith
    · -- Case where a + 1 ≠ 0
      have h_eq4 : b + 1 ≠ 0 := by
        by_contra h2
        have eq1 : -11 / (b + 1) = 0 := by
          rw [show b + 1 = (0 : ℝ) by linarith]
          norm_num
        have eq2 : -11 / (a + 1) = 0 := by 
          linarith [h_eq2, eq1]
        have h3 : a + 1 = 0 := by 
          by_contra h4
          have h5 : -11 / (a + 1) ≠ 0 := by 
            have h6 : a + 1 ≠ 0 := h4
            field_simp [h6]
          contradiction
        contradiction
      -- Cross-multiplication
      have eq1 : -11 * (b + 1) = -11 * (a + 1) := by
        have h_eq5 : -11 / (a + 1) = -11 / (b + 1) := h_eq2
        field_simp [h_eq3, h_eq4] at h_eq5 ⊢
        nlinarith 
      have eq2 : a + 1 = b + 1 := by
        nlinarith
      linarith
  · -- Show that ∀ x ∈ Ioo (-1) 10, f x < 2
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    rw [hf]
    have hx3 : x + 1 > 0 := by linarith
    have hx4 : x + 1 < 11 := by linarith
    have h1 : -11 / (x + 1) < -1 := by
      have h3 : -11 / (x + 1) + 1 < 0 := by 
        have h4 : -11 / (x + 1) + 1 = (x - 10) / (x + 1) := by 
          field_simp [show 0 < x + 1 by linarith]
          <;> ring 
        rw [h4]
        apply div_neg_of_neg_of_pos
        · linarith
        · linarith
      linarith
    have h2 : (-11 / (x + 1) + 3 ) < 2 := by 
      linarith
    simpa using h2