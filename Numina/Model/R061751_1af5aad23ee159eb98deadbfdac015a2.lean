import Mathlib
open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_899 {a b : ℝ} (ha : a ≠ b) (f : ℝ → ℝ)
    (hf : Continuous f) (h : ∀ x, f (x + a) + f (b + x) = (1 / 2) * f (2 * x))
    (h' : Tendsto (λ x => f x / x ^ 2) atTop (𝓝 0)) (h'' : Tendsto (λ x => f x / x ^ 2) atBot (𝓝 0)) :
    ∃ c, Function.Periodic f c := by 
        use 0
        simp [Function.Periodic]