import Mathlib

theorem algebra_211106 (x : ℝ) :
    abs (x - abs (x - abs (x + 1))) = x ↔ x = 1 / 2 := by
  constructor
  · -- First direction: If abs (x - abs (x - abs (x + 1))) = x, then x = 1 / 2
    intro h
    by_cases h1 : x + 1 ≥ 0
    · -- Case 1: If x + 1 ≥ 0 (i.e., x ≥ -1), then abs (x + 1) = x + 1
      have h2 : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
      rw [h2] at h
      by_cases h3 : x - abs (x - (x + 1)) ≥ 0
      · -- Subcase 1a: If x - abs (x - (x + 1)) ≥ 0, then abs (x - abs (x - (x + 1))) = x - abs (x - (x + 1))
        rw [abs_of_nonneg h3] at h
        by_cases h4 : x - (x + 1) ≥ 0
        · -- Subcase 1a1: If x - (x + 1) ≥ 0 (i.e., -1 ≥ 0, contradiction), then we proceed
          have h5 : abs (x - (x + 1)) = x - (x + 1) := abs_of_nonneg h4
          rw [h5] at h
          nlinarith
        · -- Subcase 1a2: If x - (x + 1) < 0 (which is always true), then abs (x - (x + 1)) = -(x - (x + 1))
          have h6 : abs (x - (x + 1)) = -(x - (x + 1)) := abs_of_neg (not_le.mp h4)
          rw [h6] at h
          nlinarith
      · -- Subcase 1b: If x - abs (x - (x + 1)) < 0, then abs (x - abs (x - (x + 1))) = -(x - abs (x - (x + 1)))
        rw [abs_of_neg (not_le.mp h3)] at h
        by_cases h4 : x - (x + 1) ≥ 0
        · -- Subcase 1b1: If x - (x + 1) ≥ 0 (contradiction again), then proceed
          have h5 : abs (x - (x + 1)) = x - (x + 1) := abs_of_nonneg h4
          rw [h5] at h
          nlinarith
        · -- Subcase 1b2: If x - (x + 1) < 0 (which is true), then abs (x - (x + 1)) = -(x - (x + 1))
          have h6 : abs (x - (x + 1)) = -(x - (x + 1)) := abs_of_neg (not_le.mp h4)
          rw [h6] at h
          nlinarith
    · -- Case 2: If x + 1 < 0 (i.e., x < -1), then abs (x + 1) = -(x + 1)
      have h2 : abs (x + 1) = -(x + 1) := abs_of_neg (not_le.mp h1)
      rw [h2] at h
      by_cases h3 : x - abs (x - (-(x + 1))) ≥ 0
      · -- Subcase 2a: If x - abs (x - (-(x + 1))) ≥ 0, then abs (x - abs (x - (-(x + 1)))) = x - abs (x - (-(x + 1)))
        rw [abs_of_nonneg h3] at h
        by_cases h4 : x - (-(x + 1)) ≥ 0
        · -- Subcase 2a1: If x - (-(x + 1)) ≥ 0 (i.e., 2x + 1 ≥ 0), then abs (x - (-(x + 1))) = x - (-(x + 1))
          have h5 : abs (x - (-(x + 1))) = x - (-(x + 1)) := abs_of_nonneg h4
          rw [h5] at h
          nlinarith
        · -- Subcase 2a2: If x - (-(x + 1)) < 0 (i.e., 2x + 1 < 0), then abs (x - (-(x + 1))) = -(x - (-(x + 1)))
          have h6 : abs (x - (-(x + 1))) = -(x - (-(x + 1))) := abs_of_neg (not_le.mp h4)
          rw [h6] at h
          nlinarith
      · -- Subcase 2b: If x - abs (x - (-(x + 1))) < 0, then abs (x - abs (x - (-(x + 1)))) = -(x - abs (x - (-(x + 1))))
        rw [abs_of_neg (not_le.mp h3)] at h
        by_cases h4 : x - (-(x + 1)) ≥ 0
        · -- Subcase 2b1: If x - (-(x + 1)) ≥ 0 (i.e., 2x + 1 ≥ 0, contradiction), then proceed
          have h5 : abs (x - (-(x + 1))) = x - (-(x + 1)) := abs_of_nonneg h4
          rw [h5] at h
          nlinarith
        · -- Subcase 2b2: If x - (-(x + 1)) < 0 (i.e., 2x + 1 < 0, which is true), then abs (x - (-(x + 1))) = -(x - (-(x + 1)))
          have h6 : abs (x - (-(x + 1))) = -(x - (-(x + 1))) := abs_of_neg (not_le.mp h4)
          rw [h6] at h
          nlinarith
  · -- Second direction: If x = 1 / 2, then abs (x - abs (x - abs (x + 1))) = x
    intro h
    rw [h]
    norm_num [abs_of_nonneg, abs_of_neg, le_refl, le_of_lt]
    <;> norm_num
    <;> linarith