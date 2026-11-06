import Mathlib

theorem algebra_10256 {α β : ℂ} (h : α^2-4*α+5=0) (h' : β^2-4*β+5=0) :
    ‖α‖+‖β‖=2*Real.sqrt 5 := by
  have h3 : α = 2 + Complex.I ∨ α = 2 - Complex.I := by
    have h1 : α^2 - 4 * α + 5 = 0 := h
    have eq1 : α^2 - 4 * α + 5 = (α - (2 + Complex.I)) * (α - (2 - Complex.I)) := by
      ring_nf
      simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
      <;> ring
    rw [eq1] at h1
    cases (mul_eq_zero.1 h1) with
    | inl h3 =>
      left
      exact eq_of_sub_eq_zero h3
    | inr h4 =>
      right
      exact eq_of_sub_eq_zero h4
  have h4 : β = 2 + Complex.I ∨ β = 2 - Complex.I := by
    have h1 : β^2 - 4 * β + 5 = 0 := h'
    have eq1 : β^2 - 4 * β + 5 = (β - (2 + Complex.I)) * (β - (2 - Complex.I)) := by
      ring_nf
      simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
      <;> ring
    rw [eq1] at h1
    cases (mul_eq_zero.1 h1) with
    | inl h3 =>
      left
      exact eq_of_sub_eq_zero h3
    | inr h4 =>
      right
      exact eq_of_sub_eq_zero h4
  cases h3 with
  | inl hα =>
    cases h4 with
    | inl hβ =>
      rw [hα, hβ]
      have h7 : ‖2 + Complex.I‖ = Real.sqrt 5 := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        ring_nf
      rw [h7]
      ring_nf
    | inr hβ =>
      rw [hα, hβ]
      have h7 : ‖2 + Complex.I‖ = Real.sqrt 5 := by 
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        ring_nf
      have h8 : ‖2 - Complex.I‖ = Real.sqrt 5 := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        ring_nf
      rw [h7, h8]
      ring_nf
  | inr hα =>
    cases h4 with
    | inl hβ =>
      rw [hα, hβ]
      have h7 : ‖2 - Complex.I‖ = Real.sqrt 5 := by 
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        ring_nf
      have h8 : ‖2 + Complex.I‖ = Real.sqrt 5 := by
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        ring_nf
      rw [h7, h8]
      ring_nf
    | inr hβ =>
      rw [hα, hβ]
      have h7 : ‖2 - Complex.I‖ = Real.sqrt 5 := by 
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        ring_nf
      rw [h7]
      ring_nf