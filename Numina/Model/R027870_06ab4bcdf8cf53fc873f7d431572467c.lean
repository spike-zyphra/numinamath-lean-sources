import Mathlib

open Real Set

theorem inequalities_312432 {x : ℝ} :
    (2 * abs (x - abs (x + abs (x - 1))) > abs (x + abs (x - abs (x + 1)))) ↔
    (x < 1 / 3 ∨ x > 3) := by
  constructor
  · -- Proof of the forward direction.
    intro h
    by_cases h1 : x ≥ 1
    · -- Case x ≥ 1
      have h2 : abs (x - 1) = x - 1 := abs_of_nonneg (by linarith)
      have h3 : abs (x + abs (x - 1)) = 2 * x - 1 := by
        rw [h2]
        have : abs (x + (x - 1)) = abs (2 * x - 1 : ℝ) := by ring_nf
        rw [this]
        have h4 : 2 * x - 1 ≥ 1 := by linarith
        rw [abs_of_nonneg (by linarith)]
      have h5 : abs (x - abs (x + abs (x - 1))) = abs (x - 1 : ℝ) := by
        rw [h3]
        have : abs (x - (2 * x - 1 : ℝ)) = abs (-(x - 1 : ℝ)) := by ring_nf
        rw [this]
        rw [abs_neg]
      have h6 : abs (x + abs (x - abs (x + 1))) = x + 1 := by
        have h7 : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
        have h8 : abs (x - abs (x + 1)) = 1 := by
          rw [h7]
          have : abs (x - (x + 1) : ℝ) = abs (-1 : ℝ) := by ring_nf
          rw [this]
          norm_num
        rw [h8]
        have : abs (x + (1 : ℝ)) = abs (x + 1 : ℝ) := by ring
        rw [this, abs_of_nonneg (by linarith)]
      rw [h5, h6] at h
      have h7 : abs (x - 1 : ℝ) = x - 1 := abs_of_nonneg (by linarith)
      rw [h7] at h
      right
      linarith
    · -- Case -1 ≤ x < 1
      by_cases h2 : x ≥ -1
      · -- Case -1 ≤ x < 1
        have h3 : abs (x - 1) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        have h4 : abs (x + abs (x - 1)) = 1 := by
          rw [h3]
          have : abs (x + (1 - x) : ℝ) = abs (1 : ℝ) := by ring_nf
          rw [this]
          all_goals norm_num
        have h5 : abs (x - abs (x + 1)) = 1 := by
          have h6 : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
          rw [h6]
          have : abs (x - (x + 1) : ℝ) = abs (-1 : ℝ) := by ring_nf
          rw [this]
          all_goals norm_num
        have h7 : abs (x + abs (x - abs (x + 1))) = x + 1 := by
          rw [h5]
          have : abs (x + (1 : ℝ)) = abs (x + 1 : ℝ) := by ring
          rw [this, abs_of_nonneg (by linarith)]
        have h8 : abs (x - abs (x + abs (x - 1))) = abs (x - 1 : ℝ) := by
          rw [h4]
        rw [h8, h7] at h
        have h9 : abs (x - 1 : ℝ) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        rw [h9] at h
        left
        linarith
      · -- Case x < -1
        have h1 : x < -1 := by linarith
        have h3 : abs (x - 1) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        have h4 : abs (x + abs (x - 1)) = 1 := by
          rw [h3]
          have : abs (x + (1 - x) : ℝ) = abs (1 : ℝ) := by ring_nf
          rw [this]
          all_goals norm_num
        have h5 : abs (x - abs (x + 1)) = abs (2 * x + 1 : ℝ) := by
          have h6 : abs (x + 1) = -(x + 1) := abs_of_nonpos (by linarith)
          rw [h6]
          have : abs (x - (- (x + 1)) : ℝ) = abs (2 * x + 1 : ℝ) := by ring_nf
          rw [this]
        have h7 : abs (x + abs (x - abs (x + 1))) = abs (-x - 1 : ℝ) := by
          rw [h5]
          have h8 : abs (2 * x + 1 : ℝ) = -(2 * x + 1) := by
            rw [abs_of_nonpos]
            linarith
            all_goals linarith
          rw [h8]
          have : abs (x + (- (2 * x + 1) : ℝ)) = abs (-x - 1 : ℝ) := by ring_nf
          rw [this]
        have h8 : abs (x - abs (x + abs (x - 1))) = abs (x - 1 : ℝ) := by
          rw [h4]
        rw [h8, h7] at h
        have h9 : abs (x - 1 : ℝ) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        rw [h9] at h
        have h10 : abs (-x - 1 : ℝ) = -x - 1 := by
          apply abs_of_pos
          linarith
        rw [h10] at h
        left
        linarith
  · -- Proof of the backward direction.
    rintro (h | h)
    · -- Case x < 1/3
      by_cases h1 : x ≥ -1
      · -- Case -1 ≤ x < 1/3
        have h3 : abs (x - 1) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        have h4 : abs (x + abs (x - 1)) = 1 := by
          rw [h3]
          have : abs (x + (1 - x) : ℝ) = abs (1 : ℝ) := by ring_nf
          rw [this]
          all_goals norm_num
        have h5 : abs (x - abs (x + 1)) = 1 := by
          have h6 : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
          rw [h6]
          have : abs (x - (x + 1) : ℝ) = abs (-1 : ℝ) := by ring_nf
          rw [this]
          all_goals norm_num
        have h7 : abs (x + abs (x - abs (x + 1))) = x + 1 := by
          rw [h5]
          have : abs (x + (1 : ℝ)) = abs (x + 1 : ℝ) := by ring
          rw [this, abs_of_nonneg (by linarith)]
        have h8 : abs (x - abs (x + abs (x - 1))) = abs (x - 1 : ℝ) := by
          rw [h4]
        rw [h8, h7]
        have h9 : abs (x - 1 : ℝ) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        rw [h9]
        linarith
      · -- Case x < -1
        have h1 : x < -1 := by linarith
        have h3 : abs (x - 1) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        have h4 : abs (x + abs (x - 1)) = 1 := by
          rw [h3]
          have : abs (x + (1 - x) : ℝ) = abs (1 : ℝ) := by ring_nf
          rw [this]
          all_goals norm_num
        have h5 : abs (x - abs (x + 1)) = abs (2 * x + 1 : ℝ) := by
          have h6 : abs (x + 1) = -(x + 1) := abs_of_nonpos (by linarith)
          rw [h6]
          have : abs (x - (- (x + 1)) : ℝ) = abs (2 * x + 1 : ℝ) := by ring_nf
          rw [this]
        have h7 : abs (x + abs (x - abs (x + 1))) = abs (-x - 1 : ℝ) := by
          rw [h5]
          have h8 : abs (2 * x + 1 : ℝ) = -(2 * x + 1) := by
            rw [abs_of_nonpos]
            linarith
            all_goals linarith
          rw [h8]
          have : abs (x + (- (2 * x + 1) : ℝ)) = abs (-x - 1 : ℝ) := by ring_nf
          rw [this]
        have h8 : abs (x - abs (x + abs (x - 1))) = abs (x - 1 : ℝ) := by
          rw [h4]
        rw [h8, h7]
        have h9 : abs (x - 1 : ℝ) = 1 - x := by
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        rw [h9]
        have h10 : abs (-x - 1 : ℝ) = -x - 1 := by
          apply abs_of_pos
          linarith
        rw [h10]
        linarith
    · -- Case x > 3
      have h1 : x > 3 := by linarith
      have h2 : abs (x - 1) = x - 1 := abs_of_nonneg (by linarith)
      have h3 : abs (x + abs (x - 1)) = 2 * x - 1 := by
        rw [h2]
        have : abs (x + (x - 1)) = abs (2 * x - 1 : ℝ) := by ring_nf
        rw [this]
        have h4 : 2 * x - 1 > 0 := by linarith
        rw [abs_of_pos h4]
      have h5 : abs (x - abs (x + abs (x - 1))) = abs (x - 1 : ℝ) := by
        rw [h3]
        have : abs (x - (2 * x - 1 : ℝ)) = abs (-(x - 1 : ℝ)) := by ring_nf
        rw [this]
        rw [abs_neg]
      have h6 : abs (x + abs (x - abs (x + 1))) = x + 1 := by
        have h7 : abs (x + 1) = x + 1 := abs_of_pos (by linarith)
        have h8 : abs (x - abs (x + 1)) = 1 := by
          rw [h7]
          have : abs (x - (x + 1) : ℝ) = abs (-1 : ℝ) := by ring_nf
          rw [this]
          norm_num
        rw [h8]
        have : abs (x + (1 : ℝ)) = abs (x + 1 : ℝ) := by ring
        rw [this, abs_of_pos (by linarith)]
      rw [h5, h6]
      have h7 : abs (x - 1 : ℝ) = x - 1 := abs_of_nonneg (by linarith)
      rw [h7]
      linarith