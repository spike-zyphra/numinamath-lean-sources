import Mathlib


lemma lemma_1
    (x y z : ℝ)
    (h₀ : x + y + z = 1)
    (h₁ : x^2 + y^2 + z^2 = 1) :
    x * y + y * z + z * x = 0 := by
  have h3 : x * y + y * z + z * x = 0 := by
    have eq4 : (x + y + z) ^ 2 = x^2 + y^2 + z^2 + 2 * (x * y + y * z + z * x) := by
      ring
    rw [h₀, h₁] at eq4
    norm_num at eq4
    linarith
  exact h3


theorem algebra_102767 (x y z : ℝ) (h₀ : x + y + z = 1) (h₁ : x^2 + y^2 + z^2 = 1) :
    (x^3 + y^3 + z^3 ≥ 5 / 9) ∧
    (∃ x0 y0 z0: ℝ, (x0 + y0 + z0 = 1) ∧ (x0^2 + y0^2 + z0^2 = 1) ∧ (x0^3 + y0^3 + z0^3 = 5/9)) := by
  have h2 : x * y + y * z + z * x = 0 := lemma_1 x y z h₀ h₁
  have eq3 : x^3 + y^3 + z^3 - 3 * (x * y * z) = (x + y + z) * ((x^2 + y^2 + z^2) - (x * y + y * z + z * x)) := by
    ring
  rw [h₀, h₁, h2] at eq3
  have eq4 : x^3 + y^3 + z^3 = 1 + 3 * (x * y * z) := by 
    nlinarith
  constructor
  · -- Proof that x^3 + y^3 + z^3 ≥ 5/9
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 2/3), sq_nonneg (y - 2/3), sq_nonneg (z + 1/3),
      sq_nonneg (x + 1/3), sq_nonneg (y + 1/3), sq_nonneg (z - 2/3)]
  · -- Proof that there exist values for x, y, z that equals 5/9
    use 2 / 3, 2 / 3, -1 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num