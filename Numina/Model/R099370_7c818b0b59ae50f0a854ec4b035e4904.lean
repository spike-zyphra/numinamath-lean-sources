import Mathlib

theorem algebra_12865 {φ ψ ω : ℝ → ℝ}
    (hφ : Function.LeftInverse ψ φ)
    (hψ : Function.RightInverse ψ φ)
    (hω : ∀ x, ω (-x) = -ψ x) :
    ω = fun x => -ψ (-x) := by 
        funext x
        specialize hω (-x)
        simp at hω ⊢
        linarith