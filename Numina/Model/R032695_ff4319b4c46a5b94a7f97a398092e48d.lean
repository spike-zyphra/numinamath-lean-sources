import Mathlib

open Real Set

theorem algebra_11687 :
    IsLeast {z : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ z = (x + 1 / y) * (x + 1 / y - 2018) +
      (y + 1 / x) * (y + 1 / x - 2018)} (-2036162) := by
  constructor 
  · -- First, we need to prove that -2036162 is in the set.
    use (1009 + Real.sqrt 1018077) / 2, (1009 + Real.sqrt 1018077) / 2
    constructor
    · -- Show x > 0.
      nlinarith [Real.sqrt_nonneg 1018077, Real.sq_sqrt (show 0 ≤ (1018077 : ℝ) by nlinarith)]
    constructor 
    · -- Show y > 0.
      nlinarith [Real.sqrt_nonneg 1018077, Real.sq_sqrt (show 0 ≤ (1018077 : ℝ) by nlinarith)]
    · -- Verify the value.
      field_simp 
      nlinarith [Real.sqrt_nonneg 1018077, Real.sq_sqrt (show 0 ≤ (1018077 : ℝ) by nlinarith)]
  · -- Second, we need to prove that -2036162 is the minimum value.
    intro z h
    rcases h with ⟨x, y, hx, hy, hz⟩
    have h1 : (x + 1 / y) + (y + 1 / x) ≥ 4 := by
      have h1 : x + 1 / x ≥ 2 := by
        have h3 : x ≥ 0 := by linarith
        have h4 : x + 1 / x - 2 ≥ 0 := by
          have h11 : x + 1 / x - 2 = (x - 1)^2 / x := by
            field_simp 
            ring 
          rw [h11]
          apply div_nonneg
          · nlinarith [sq_nonneg (x - 1)]
          all_goals linarith
        linarith
      have h2 : y + 1 / y ≥ 2 := by
        have h4 : y ≥ 0 := by linarith
        have h5 : y + 1 / y - 2 ≥ 0 := by
          have h11 : y + 1 / y - 2 = (y - 1)^2 / y := by
            field_simp 
            ring 
          rw [h11]
          apply div_nonneg 
          · nlinarith [sq_nonneg (y - 1)]
          all_goals linarith
        linarith
      linarith
    nlinarith [sq_nonneg ((x + 1 / y) - (y + 1 / x)), sq_nonneg ((x + 1 / y) - 1009), sq_nonneg ((y + 1 / x) - 1009), sq_nonneg (x - y), sq_nonneg (x * y - 1)]