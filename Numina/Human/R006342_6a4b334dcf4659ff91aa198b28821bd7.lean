import Mathlib

/-A grocery store owner has three types of currency: 1-jiao items, 5-jiao items, and 100-jiao items. The owner bundles these items separately by type. Each bundle contains exactly $M$ items of a single type. If the owner has one bundle of each type of item, determine the total value of the items in jiao. Show the answer is $106M$ jiao.-/
theorem total_value_currency
  (x₁ x₂ x₃: ℕ) (M: ℝ)
  (h : x₁ = 1 ∧ x₂ = 5 ∧ x₃ = 100) :
  x₁ * M + x₂ * M + x₃ * M = 106 * M := by
  -- Extract the three equalities from the conjunction `h`.
  rcases h with ⟨h1, h2, h3⟩
  -- Substitute the values
  rw [h1, h2, h3]
  -- The goal reduces to `1 * M + 5 * M + 100 * M = 106 * M`, which `ring` solves.
  ring
