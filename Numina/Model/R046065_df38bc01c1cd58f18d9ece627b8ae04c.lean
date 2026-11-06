import Mathlib

theorem algebra_14938 {pre A B C D E : Prop}
    (hA : A = (∀ a b c : ℝ, a < 0 ∧ a < b ∧ b < c → (a * b < b * c)))
    (hB : B = (∀ a b c : ℝ, a < 0 ∧ a < b ∧ b < c → (a * c < b * c)))
    (hC : C = (∀ a b c : ℝ, a < 0 ∧ a < b ∧ b < c → (a * b < a * c)))
    (hD : D = (∀ a b c : ℝ, a < 0 ∧ a < b ∧ b < c → (a + b < b + c)))
    (hE : E = (∀ a b c : ℝ, a < 0 ∧ a < b ∧ b < c → (c / a < 1))) :
    D ∧ E ∧
    ¬ A ∧ ¬ B ∧ ¬ C := by
  have h1 : D := by 
    rw [hD]
    intro a b c h 
    have h1 : a < 0 := h.1 
    have h2 : a < b := h.2.1 
    have h3 : b < c := h.2.2 
    linarith 
  have h2 : E := by 
    rw [hE]
    intro a b c h 
    have h1 : a < 0 := h.1 
    have h2 : a < b := h.2.1 
    have h3 : b < c := h.2.2 
    have h4 : c > a := by linarith 
    have h5 : c / a < 1 := by 
      apply (div_lt_iff_of_neg' (by linarith)).mpr 
      linarith 
    linarith 
  have h3 : ¬A := by 
    rw [hA]
    intro h 
    specialize h (-1 : ℝ) (-0.5 : ℝ) (0 : ℝ) ⟨by norm_num, by norm_num, by norm_num⟩ 
    norm_num at h 
  have h4 : ¬B := by 
    rw [hB]
    intro h 
    specialize h (-1 : ℝ) (-0.5 : ℝ) (0 : ℝ) ⟨by norm_num, by norm_num, by norm_num⟩ 
    norm_num at h 
  have h5 : ¬C := by 
    rw [hC]
    intro h 
    specialize h (-1 : ℝ) (-0.5 : ℝ) (0 : ℝ) ⟨by norm_num, by norm_num, by norm_num⟩ 
    norm_num at h 
  exact ⟨h1, h2, h3, h4, h5⟩