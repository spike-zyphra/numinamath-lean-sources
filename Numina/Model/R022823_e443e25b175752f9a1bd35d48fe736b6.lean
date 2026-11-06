import Mathlib


lemma lemma_1 : (2^12) ≡ 1 [ZMOD 13] := by
  native_decide


theorem algebra_203429 {α β γ δ : ℝ}
    (hα : α = 2^1000 % 13) (hβ : β = ((7 + 4 * Real.sqrt α)^(1 / 2) - (7 - 4 * Real.sqrt α)^(1 / 2)) / Real.sqrt α)
    (hf : ∀ a, a - β = (7 + 4 * Real.sqrt α)^(1 / 2) - (7 - 4 * Real.sqrt α)^(1 / 2)) (hF : ∀ a b, b^2 + a = γ)
    (hδ : δ = ∏ᶠ x ∈ {x | x > 0 ∧ x^(Real.logb 7 x) = 10}, x) :
    α = 1 ∧ β = 1 ∧ γ = 1 ∧ δ = 1 := by 
  have h1' := hf 0
  have h2' := hf 4
  norm_num at h1' h2'
  all_goals 
    nlinarith