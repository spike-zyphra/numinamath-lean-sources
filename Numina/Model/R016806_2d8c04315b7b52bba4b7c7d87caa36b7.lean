import Mathlib

theorem algebra_178100 (f g : ℝ → ℝ)
    (hf : f = fun x => -x^2 + 4 * x + 4) (hg : g = fun x => x^2 - 2 * x + 4) :
    ∃ α₁ α₂, α₁ ∈ Set.range (fun x => Real.arctan (x / 7)) ∧
    α₂ ∈ Set.range (fun x => -Real.arctan (x / 7)) ∧
    α₁ ≠ α₂ := by
  use Real.pi / 4, -Real.pi / 4
  constructor
  · -- Show that π/4 is in the range of arctan(x/7)
    use 7
    all_goals
    have h1 : Real.arctan ((7 : ℝ) / 7) = Real.pi / 4 := by
      have h2 : (7 : ℝ) / 7 = 1 := by norm_num
      rw [h2]
      have h3 : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
      linarith
    linarith [h1]
  constructor
  · -- Show that -π/4 is in the range of -arctan(x/7)
    use 7
    all_goals
    have h1 : -Real.arctan ((7 : ℝ) / 7) = - (Real.pi / 4) := by
      have h2 : Real.arctan ((7 : ℝ) / 7) = Real.pi / 4 := by
        have h3 : (7 : ℝ) / 7 = 1 := by norm_num
        rw [h3]
        have h4 : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
        linarith
      linarith
    linarith [h1]
  · -- Show that π/4 ≠ -π/4
    have h1 : Real.pi / 4 > 0 := by
      linarith [Real.pi_pos]
    intro h
    have h2 : Real.pi / 4 + Real.pi / 4 = 0 := by linarith
    have h3 : Real.pi / 2 = 0 := by
      linarith
    have h4 : Real.pi > 0 := Real.pi_pos
    nlinarith