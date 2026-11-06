import Mathlib

open BigOperators Real Set

theorem algebra_20652 :
    {r : ℝ | ∃ x y z : ℝ, x + y + z = 7 ∧ x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ r = x * y * z} = Set.Icc 0 (343 / 27) := by 
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- First direction: if r is in the image of f, then r is in [0, 343/27]
    rintro ⟨x, y, z, h_eq, hx, hy, hz, hr⟩
    have h1 : x * y * z ≥ 0 := by
      apply mul_nonneg
      apply mul_nonneg
      all_goals linarith
    have h2 : x * y * z ≤ 343 / 27 := by
      have h34 : x * y * z ≤ (7 / 3) ^ 3 := by
        have h4 : (x + y + z : ℝ) = 7 := by linarith
        have h5 : x * y * z ≤ ((x + y + z) / 3) ^ 3 := by
          nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x - (x + y + z) / 3), sq_nonneg (y - (x + y + z) / 3), sq_nonneg (z - (x + y + z) / 3),
            mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), 
            mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ z by linarith), 
            mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ z by linarith)]
        have h37 : ((x + y + z) / 3 : ℝ) = 7 / 3 := by linarith
        rw [h37] at h5
        linarith
      norm_num at h34 ⊢
      linarith
    constructor
    · -- Show r ≥ 0
      nlinarith [hr, h1]
    · -- Show r ≤ 343/27
      nlinarith [hr, h2]
  · -- Second direction: if r is in [0, 343/27], then r is in the image of f.
    rintro ⟨hr1, hr2⟩
    have h12 : r ≤ 343 / 27 := by linarith
    have h34 : ∃ x y z : ℝ, x + y + z = 7 ∧ x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ r = x * y * z := by
      use (7 / 3) * (1 + Real.sqrt (1 - (27 / 343) * r)), (7 / 3) * (1 : ℝ), (7 / 3) * (1 - Real.sqrt (1 - (27 / 343) * r))
      constructor
      · -- Show x+y+z=7
        nlinarith [Real.sqrt_nonneg (1 - (27 / 343) * r), Real.sq_sqrt (show 0 ≤ 1 - (27 / 343) * r by nlinarith)]
      constructor
      · -- Show x >=0
        nlinarith [Real.sqrt_nonneg (1 - (27 / 343) * r), Real.sq_sqrt (show 0 ≤ 1 - (27 / 343) * r by nlinarith), sq_nonneg (Real.sqrt (1 - (27 / 343) * r) - 1)]
      constructor
      · -- Show y >=0
        nlinarith
      constructor
      · -- Show z >=0
        nlinarith [Real.sqrt_nonneg (1 - (27 / 343) * r), Real.sq_sqrt (show 0 ≤ 1 - (27 / 343) * r by nlinarith), sq_nonneg (Real.sqrt (1 - (27 / 343) * r) - 1)]
      · -- Show r = x*y*z
        nlinarith [Real.sqrt_nonneg (1 - (27 / 343) * r), Real.sq_sqrt (show 0 ≤ 1 - (27 / 343) * r by nlinarith), sq_nonneg (Real.sqrt (1 - (27 / 343) * r) - 1)]
    simpa using h34