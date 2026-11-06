import Mathlib

open Real

theorem calculus_190219 : 
    ∃ f : ℝ → ℝ, ∃ x₀ δ : ℝ, δ > 0 ∧ 
    DifferentiableOn ℝ f (Set.Ioo (x₀-δ) (x₀+δ)) ∧ 
    IsMaxOn f (Set.Ioo (x₀-δ) (x₀+δ)) x₀ ∧
    ¬∃ δ' : ℝ, δ' > 0 ∧ δ' < δ ∧ 
    ∀ x ∈ Set.Ioo (x₀-δ') x₀, deriv f x > 0 ∧
    ∀ x ∈ Set.Ioo x₀ (x₀+δ'), deriv f x < 0 := by 
  use (fun _ : ℝ => (0 : ℝ))
  use (0 : ℝ)
  use 1
  constructor
  · -- Show δ > 0
    norm_num
  constructor
  · -- show DifferentiableOn ℝ f (Set.Ioo (0 - 1) (0 + 1))
    apply differentiableOn_const
  constructor
  · -- show IsMaxOn f (Set.Ioo (0 - 1) (0 + 1)) 0
    unfold IsMaxOn
    intro x hx
    rw [Set.mem_Ioo] at hx
    norm_num
  · -- show ¬∃ δ' : ℝ, δ' > 0 ∧ δ' < δ ∧ 
    intro h
    rcases h with ⟨δ', h1, h2, h3⟩ 
    have h4 := h3 (0 - δ' / 2) (by
      constructor
      · -- Show that $0 - \delta'/2 > -\delta'$
        nlinarith [show δ' > 0 by linarith]
      · -- Show that $0 - \delta'/2 < 0$
        nlinarith [show δ' > 0 by linarith]
    )
    have h5 : deriv (fun (_ : ℝ) => (0 : ℝ)) (0 - δ' / 2) = 0 := by
      simp
    linarith [h5, h4.1]