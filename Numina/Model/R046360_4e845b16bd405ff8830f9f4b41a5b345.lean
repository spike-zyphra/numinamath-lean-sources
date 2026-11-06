import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_18794 (f : ℝ → ℝ) (hf : f = λ x => sqrt (x ^ 2)) :
    range f = {y | 0 ≤ y} := by 
  ext y 
  simp [hf]
  constructor 
  · -- Assume $y \in range(f)$, we need to prove $0 \leq y$
    rintro ⟨x, hx⟩
    have h1 : sqrt (x ^ 2) ≥ 0 := by positivity 
    have eq1 : sqrt (x ^ 2) = y := by
      linarith 
    linarith 
  · -- Assume $0 \leq y$, we need to prove $y \in range(f)$
    intro hy 
    use y 
    have h1 : 0 ≤ y := hy 
    have h2 : sqrt (y ^ 2) = y := by 
      rw [Real.sqrt_sq (show 0 ≤ y by linarith)]
    linarith [h2]