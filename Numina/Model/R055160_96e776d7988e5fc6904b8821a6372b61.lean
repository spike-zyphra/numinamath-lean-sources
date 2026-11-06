import Mathlib

theorem algebra_141927 {φ ψ ω : ℝ → ℝ} (hφ : Function.LeftInverse ψ φ)
    (hψ : Function.RightInverse ψ φ) (hω : ∀ x, ω (-x) = -ψ x) :
    ω = fun x => -ψ (-x) := by 
  funext x
  have h1 : ω x = -ψ (-x) := by 
    specialize hω (-x)
    simp at hω 
    linarith 
  exact h1