import Mathlib

theorem algebra_128460 (a : ℝ) :
    (∃ x y, x^2 + 4 * (y - a)^2 = 4 ∧ y = x^2 / 2) ↔ a ∈ Set.Icc (-1) (17 / 8) := by
  constructor
  · -- Assume there exists x, y such that both equations hold, prove a ∈ [-1, 17/8]
    rintro ⟨x, y, h1, h2⟩
    have h3 : x^2 + 4 * (y - a)^2 = 4 := h1
    rw [show y = x^2 / 2 by linarith [h2]] at h3
    have h4 : x^2 ≥ 0 := by nlinarith
    have h5 : (x^2) ^ 2 + (1 - 4 * a) * (x^2) + (4 * a^2 - 4) = 0 := by
      nlinarith 
    have h6 : (17 - 8 * a) ≥ 0 := by
      nlinarith [ sq_nonneg (x^2 + (1 - 4 * a) / 2 ), sq_nonneg (x^2 - 2 * a) ]
    constructor
    · -- Show that a ≥ -1
      nlinarith [ sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 2 * a), sq_nonneg (a + 1) ]
    · -- Show that a ≤ 17/8
      nlinarith
  · -- Assume a ∈ [-1, 17/8], prove there exists x, y
    rintro (h : a ∈ Set.Icc (-1) (17 / 8))
    rcases h with ⟨ha1, ha2⟩
    have h7 : (17 - 8 * a) ≥ 0 := by
      nlinarith
    have h8 : ∃ z, z ≥ 0 ∧ z ^ 2 + (1 - 4 * a) * z + (4 * a^2 - 4) = 0 := by
      use (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2
      constructor
      · -- Show z ≥ 0
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show 17 - 8 * a ≥ 0 by nlinarith) ]
      · -- Show quadratic is 0
        nlinarith [ Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show 17 - 8 * a ≥ 0 by nlinarith) ]
    rcases h8 with ⟨z, hz1, hz2⟩
    use Real.sqrt z, z / 2
    constructor
    · -- Show x^2 + 4 * (y - a)^2 = 4
      have h9 : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (by nlinarith)
      nlinarith [ h9 ]
    · -- Show y = x^2 / 2
      all_goals nlinarith [ Real.sq_sqrt (show z ≥ 0 by nlinarith) ]