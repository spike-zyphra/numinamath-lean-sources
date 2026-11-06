import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_192619 {f : ℝ → ℝ} (hf : ∃ a, a ≠ 0 ∧ f = λ x => sqrt (a * x + 4))
  (hinv : ∃ g : ℝ → ℝ, ∀ x, g (f x) = x ∧ ∀ x, f (g x) = x ∧
    {x | f x = g x}.encard = 3) :
  a ∈ Ioo (-1) 0 := by

  rcases hf with ⟨a, ha1, hf⟩
  rcases hinv with ⟨g, hg⟩
  have h1 := hg 0
  rcases h1 with ⟨h11, h12⟩

  have h9 := h12 (-1)
  have h10 : f (g (-1)) = sqrt (a * (g (-1)) + 4) := by
    rw [hf]
  rw [h10] at h9
  have h11 : sqrt (a * (g (-1)) + 4) ≥ 0 := by
    apply Real.sqrt_nonneg
  nlinarith