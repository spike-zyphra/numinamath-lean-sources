import Mathlib

open Nat Filter Function
open scoped Topology

theorem number_theory_271530 (q : ℕ → ℕ)
  (h₀ : ∀ n, IsLeast {p | p.Prime ∧ ¬ p ∣ n} (q n)) :
  Tendsto (λ n => (q n : ℝ) / n) atTop (𝓝 0) := by
  have h1 := h₀ 0
  have h2 : (q 0) ∈ {p | p.Prime ∧ ¬ p ∣ 0} := by 
    exact h1.left
  have h3 : (q 0).Prime := by 
    simpa using h2.left
  have h4 : ¬(q 0) ∣ 0 := by 
    simpa using h2.right
  have h5 : (q 0) ∣ 0 := by 
    simp 
  contradiction