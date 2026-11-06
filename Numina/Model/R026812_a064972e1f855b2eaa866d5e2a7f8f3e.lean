import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_263741 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = (x + y) / (x ^ 2 + y ^ 2)) :
  {z | ∃ x y, z = f x y ∧ x + y ≥ 1} = {z | 0 < z ∧ z ≤ 2} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume z is in the image
    rintro ⟨x, y, h_eq, h_sum⟩
    rw [h₀ x y] at h_eq
    have h1 : x ^ 2 + y ^ 2 > 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1)]
    constructor
    · -- Show z > 0
      have h2 : 0 < (x + y) / (x ^ 2 + y ^ 2) := by
        apply div_pos
        linarith
        all_goals
          nlinarith
      linarith [h_eq, h2]
    · -- Show z ≤ 2
      -- We need to show that $\frac{x+y}{x^2+y^2} \leq 2$
      have h5 : (x + y) ≤ 2 * (x^2 + y^2) := by
        have h6 : 2 * (x^2 + y^2) ≥ (x + y) ^ 2 := by
          linarith [sq_nonneg (x - y)]
        have h7 : (x + y) ^ 2 ≥ x + y := by
          nlinarith [h_sum]
        linarith [h6, h7]
      have h6 : (x + y) / (x ^ 2 + y ^ 2) ≤ 2 := by
        have h7 : x ^ 2 + y ^ 2 > 0 := h1
        apply (div_le_iff₀ (by linarith)).mpr
        linarith [h5]
      linarith [h_eq, h6]
  · -- Assume $0 < z \leq 2$
    rintro ⟨hz1, hz2⟩
    use (1 / z), (1 / z)
    constructor
    · -- Show $z = f(1/z, 1/z)$
      rw [h₀]
      field_simp
      <;> ring
    · -- Show x + y ≥ 1
      have h3 : (1 / z : ℝ) + (1 / z) ≥ 1 := by
        have h4 : z > 0 := hz1
        have h5 : z ≤ 2 := hz2
        have h6 : (1 / z + 1 / z : ℝ) = 2 / z := by
          field_simp
          <;> ring
        have h7 : 2 / z ≥ 1 := by
          apply (le_div_iff₀ (by linarith)).mpr
          nlinarith
        linarith [h6, h7]
      linarith