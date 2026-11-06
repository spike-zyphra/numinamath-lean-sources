import Mathlib

theorem algebra_19966 (x : ℝ) :
    -6 * x ^ 2 + 11 * x - 4 ≥ 0 ↔ x ∈ Set.Icc (1 / 2) (4 / 3) := by 
  constructor
  · -- Assume \( -6x^2 + 11x - 4 \geq 0 \), we need to show \( x \in \left[ \frac{1}{2}, \frac{4}{3} \right] \)
    intro h
    have h1 : (x - 1 / 2) * (x - 4 / 3) ≤ 0 := by
      nlinarith
    constructor
    · -- Show \( \frac{1}{2} \leq x \)
      nlinarith 
    · -- Show \( x \leq \frac{4}{3} \)
      nlinarith 
  · -- Assume \( x \in \left[ \frac{1}{2}, \frac{4}{3} \right] \), we need to show \( -6x^2 + 11x - 4 \geq 0 \)
    rintro ⟨hx1, hx2⟩
    nlinarith