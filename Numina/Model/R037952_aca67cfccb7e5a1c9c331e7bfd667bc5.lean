import Mathlib

theorem algebra_147153 {z₁ z₂ : ℂ} {div : ℂ → ℂ → WithTop ℂ} (hz1 : z₁ ≠ z₂)
  (hd : div = fun a b ↦ if b = 0 then ⊤ else ↑(a / b)) :
  ∃ a b c d,
  let f := fun z ↦ div (a * z + b) (c * z + d)
  f z₁ = 0 ∧ f z₂ = ⊤ := by

  use 1, -z₁, 1, -z₂
  have h1 : (1 * z₁ + -z₁) = 0 := by 
    simp
  have h2 : (1 * z₂ + -z₂) = 0 := by 
    simp
  have h5 : z₁ + (-z₂) ≠ 0 := by 
    intro h_eq
    have h_eq1 : z₁.re = z₂.re := by
      simp [Complex.ext_iff] at h_eq ⊢
      all_goals try linarith 
    have h_eq2 : z₁.im = z₂.im := by 
      simp [Complex.ext_iff] at h_eq ⊢
      all_goals try linarith 
    have h_eq3 : z₁ = z₂ := by 
      simp [Complex.ext_iff, h_eq1, h_eq2] 
    contradiction 
  have h3 : (fun z : ℂ ↦ div (1 * z + -z₁) (1 * z + -z₂)) z₁ = 0 := by
    simp [hd, h1, h5]
    all_goals try { tauto }
  have h6 : (fun z : ℂ ↦ div (1 * z + -z₁) (1 * z + -z₂)) z₂ = ⊤ := by
    simp [hd, h2]
  exact ⟨h3, h6⟩