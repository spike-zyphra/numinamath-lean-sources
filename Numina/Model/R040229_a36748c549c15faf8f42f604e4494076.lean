import Mathlib

theorem number_theory_257076 {a b p α β : ℤ} (hp : Prime p) (hα : p ∣ a * α + b)
    (hβ : p ∣ a * β + b) (hdiff : ¬p ∣ α - β) :
    p ∣ a ∧ p ∣ b ∧ ∀ x, p ∣ a * x + b := by

  have h1 : p ∣ (a * β + b - (a * α + b)) := by 
    apply dvd_sub 
    exact hβ 
    exact hα 
  have h2 : a * β + b - (a * α + b) = a * (β - α) := by 
    ring
  have h3 : p ∣ a * (β - α) := by 
    rw [h2] at h1 
    exact h1 
  have ha1 : p ∣ a := by 
    have h4 : p ∣ a * (β - α) := h3 
    have h5 : p ∣ a ∨ p ∣ β - α := (Prime.dvd_mul hp).mp h4 
    have h5a : ¬p ∣ (β - α) := by 
      by_contra h 
      have h6 : p ∣ α - β := by 
        have eq1 : α - β = - (β - α) := by 
          ring 
        rw [eq1] 
        apply dvd_neg.mpr 
        exact h 
      exact hdiff h6 
    cases h5 with 
    | inl h => 
      exact h 
    | inr h => 
      exfalso 
      exact h5a h 
  have h8 : p ∣ b := by 
    have h9 : p ∣ (a * α + b) := hα 
    have ha2 : p ∣ a := ha1 
    have h91 : p ∣ a * α := by 
      apply dvd_mul_of_dvd_left 
      exact ha1 
    have h92 : p ∣ ((a * α + b) - (a * α)) := by 
      apply dvd_sub 
      exact h9 
      exact h91 
    have h93 : (a * α + b) - (a * α) = b := by 
      ring 
    rw [h93] at h92 
    exact h92 
  have h9 : ∀ x, p ∣ a * x + b := by 
    intro x 
    have h11 : p ∣ a := ha1 
    have h12 : p ∣ b := h8 
    have h13 : p ∣ a * x := by 
      apply dvd_mul_of_dvd_left 
      exact h11 
    apply dvd_add 
    exact h13 
    exact h12 
  constructor 
  · exact ha1 
  constructor 
  · exact h8 
  · exact h9