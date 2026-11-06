import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_147452 {f : ℝ → ℝ} (hf : f = λ x => 1 / 2 - 1 / 2 * cos x) :
    ¬ (∀ x, f x = 0 ↔ ∃ k : ℤ, x = k * π) := by 
  intro h
  have h1 := h Real.pi
  have h2 : f Real.pi = 1 := by
    rw [hf]
    have hcos : Real.cos Real.pi = -1 := Real.cos_pi
    simp [hcos]
    all_goals linarith
  have h3 : (f Real.pi = 0) ↔ (∃ k : ℤ, Real.pi = k * π) := h1
  have h4 : ¬ (f Real.pi = 0) := by 
    rw [show f Real.pi = 1 by linarith [h2] ]
    norm_num
  have h5 : (∃ k : ℤ, Real.pi = k * π) := by
    use 1
    all_goals
    simp
  have h7 : (f Real.pi = 0) ↔ (∃ k : ℤ, Real.pi = k * π) := h3
  have h81 : f Real.pi = 0 := h7.mpr h5
  contradiction