import Mathlib

theorem algebra_197443 (θ : ℝ) (f : ℝ → ℝ) (hf : f = fun x => x^2 + 2 * x * Real.sin θ + 1) :
    ∃ x, x ∈ Set.Icc (-1) 1 ∧ f x = -x^2 + 1 := by
  use 0
  constructor
  · -- Show that 0 is in the interval [-1, 1]
    exact ⟨by norm_num, by norm_num⟩
  · -- Show that f 0 = -0^2 + 1
    simp [hf]
    <;> norm_num