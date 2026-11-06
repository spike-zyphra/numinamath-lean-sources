import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22624 (p : ℝ → ℝ) (hp : p = λ x => x ^ 2 + 4 * x + 4) :
    range p = {y | 0 ≤ y} := by
  have h1 : ∀ x : ℝ, p x = (x + 2) ^ 2 := by 
    intro x
    rw [hp]
    ring
  ext y
  simp [h1, mem_range]
  constructor
  · -- Assume y in range p, so there is an x such that (x + 2)^2 = y, which implies y ≥ 0
    rintro ⟨x, hx⟩
    have : (x + 2) ^ 2 ≥ 0 := by apply sq_nonneg
    linarith
  · -- Assume y ≥ 0, need to find x such that (x + 2)^2 = y
    intro hy
    use Real.sqrt y - 2
    have h2 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)
    have h3 : (Real.sqrt y - 2 + 2) ^ 2 = (Real.sqrt y) ^ 2 := by ring
    linarith