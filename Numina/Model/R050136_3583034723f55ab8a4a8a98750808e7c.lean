import Mathlib

theorem algebra_297428 {α β : ℝ} (h : 2*α^2-3*abs α-2=0) (h' : 2*β^2-3*abs β-2=0)
    (h'' : α≠β) : α*β/(abs α+abs β)=-1 := by
  have h1 : α = 2 ∨ α = -2 := by
    by_cases hα : α ≥ 0
    · -- If α ≥ 0, then |α| = α
      rw [abs_of_nonneg hα] at h
      have h2 : 2 * α^2 - 3 * α - 2 = 0 := by linarith
      have h3 : (2 * α + 1) * (α - 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h3) with
      | inl h4 =>
        have h5 : α < 0 := by nlinarith
        linarith
      | inr h6 =>
        have h7 : α = 2 := by linarith
        left
        linarith
    · -- If α < 0, then |α| = -α
      rw [abs_of_neg (lt_of_not_ge hα)] at h
      have h2 : 2 * α^2 + 3 * α - 2 = 0 := by linarith
      have h3 : (2 * α - 1) * (α + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h3) with
      | inl h4 =>
        have h5 : α > 0 := by nlinarith
        linarith
      | inr h6 =>
        have h7 : α = -2 := by linarith
        right
        linarith
  have h2 : β = 2 ∨ β = -2 := by
    by_cases hβ : β ≥ 0
    · -- If β ≥ 0, then |β| = β
      rw [abs_of_nonneg hβ] at h'
      have h2 : 2 * β^2 - 3 * β - 2 = 0 := by linarith
      have h3 : (2 * β + 1) * (β - 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h3) with
      | inl h4 =>
        have h5 : β < 0 := by nlinarith
        linarith
      | inr h6 =>
        have h7 : β = 2 := by linarith
        left
        linarith
    · -- If β < 0, then |β| = -β
      rw [abs_of_neg (lt_of_not_ge hβ)] at h'
      have h2 : 2 * β^2 + 3 * β - 2 = 0 := by linarith
      have h3 : (2 * β - 1) * (β + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h3) with
      | inl h4 =>
        have h5 : β > 0 := by nlinarith
        linarith
      | inr h6 =>
        have h7 : β = -2 := by linarith
        right
        linarith
  cases h1 with
  | inl hα =>
    cases h2 with
    | inl hβ =>
      exfalso
      exact h'' (by linarith)
    | inr hβ =>
      rw [hα, hβ]
      norm_num [abs_of_nonneg, abs_of_neg]
  | inr hα =>
    cases h2 with
    | inl hβ =>
      rw [hα, hβ]
      norm_num [abs_of_nonneg, abs_of_neg]
    | inr hβ =>
      exfalso
      exact h'' (by linarith)