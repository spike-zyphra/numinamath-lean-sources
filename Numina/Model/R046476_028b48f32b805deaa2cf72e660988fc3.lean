import Mathlib

theorem algebra_250439 : (5 * (6 : ℝ) ^ ((1 : ℝ) / 3) - 2 * (12 : ℝ) ^ ((1 : ℝ) / 3)) /
    (4 * (12 : ℝ) ^ ((1 : ℝ) / 3) + 2 * (6 : ℝ) ^ ((1 : ℝ) / 3)) =
    (24 * (4 : ℝ) ^ ((1 : ℝ) / 3) - 12 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 11) / 34 := by

  have h1 : (12 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((1 : ℝ) / 3) * (6 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h2 : (12 : ℝ) = (2 : ℝ) * (6 : ℝ) := by norm_num
    rw [h2]
    have h3 : ((2 : ℝ) * (6 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((1 : ℝ) / 3) * (6 : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals
        norm_num
    linarith

  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    have h5 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [h5]
    rw [← Real.rpow_mul]
    norm_num
    all_goals linarith

  have h7 : (2 : ℝ) ^ ((2 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    have h8 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals linarith
    linarith

  -- Let's rewrite the right side using h4 and h7.
  have h8 : (24 * (4 : ℝ) ^ ((1 : ℝ) / 3) - 12 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 11) / 34 =
          (24 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - 12 * (2 : ℝ) ^ ((1 : ℝ) / 3) - 11) / 34 := by
    have h7' : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
      have h4' : (4 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) := h4
      rw [h4']
      have h7' : (2 : ℝ) ^ ((2 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := h7
      rw [h7']
    rw [h7']

  rw [h1, h8]

  -- Now the left side is written in terms of (2: ℝ)^(1/3) and (6: ℝ)^(1/3).
  -- The right side is written in terms of powers of (2: ℝ)^(1/3).

  -- Now, we can simplify the left side
  -- Numerator: 5 * (6 : ℝ) ^ (1/3) - 2 * (2^(1/3) * 6^(1/3)) = (5 - 2 * 2^(1/3)) * 6^(1/3)
  -- Denominator: 4 * (2^(1/3) * 6^(1/3)) + 2 * (6 : ℝ) ^ (1/3) = (4 * 2^(1/3) + 2) * 6^(1/3)
  -- Therefore, left side becomes (5 - 2 * 2^(1/3)) / (4 * 2^(1/3) + 2)
  have h9 : ( (5 * (6 : ℝ) ^ ((1 : ℝ) / 3) - 2 * ((2 : ℝ) ^ ((1 : ℝ) / 3) * (6 : ℝ) ^ ((1 : ℝ) / 3)) ) / (4 * ((2 : ℝ) ^ ((1 : ℝ) / 3) * (6 : ℝ) ^ ((1 : ℝ) / 3)) + 2 * (6 : ℝ) ^ ((1 : ℝ) / 3)) ) =
          (5 - 2 * (2 : ℝ) ^ ((1 : ℝ) / 3)) / (4 * (2 : ℝ) ^ ((1 : ℝ) / 3) + 2) := by
    have hn1 : (6 : ℝ) ^ ((1 : ℝ) / 3) ≠ 0 := by
      positivity
    have hn2 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≠ 0 := by
      positivity
    have hn3 : (4 * ((2 : ℝ) ^ ((1 : ℝ) / 3) * (6 : ℝ) ^ ((1 : ℝ) / 3)) + 2 * (6 : ℝ) ^ ((1 : ℝ) / 3)) ≠ 0 := by
      positivity
    field_simp [hn3, hn1, hn2]
    <;> ring

  rw [h9]

  -- Now the goal is to show (5 - 2 * 2^(1/3)) / (4 * 2^(1/3) + 2) = (24 * (2^(1/3))^2 - 12 * 2^(1/3) - 11) / 34
  -- To prove this, we'll cross multiply and show the equality.
  have h10 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num

  have h11 : (4 * (2 : ℝ) ^ ((1 : ℝ) / 3) + 2) ≠ 0 := by
    positivity

  field_simp [h11]
  -- Now, expand both sides
  -- Multiply the right side.
  -- For the right side, we need to expand:
  -- (24 * (2^(1/3))^2 - 12 * 2^(1/3) - 11) * (4 * 2^(1/3) + 2)
  -- Expanding:
  -- (24 * (2^(1/3))^2) * (4 * 2^(1/3)) = 24 * 4 * (2^(1/3))^3 = 96 * 2 = 192
  -- (24 * (2^(1/3))^2) * 2 = 48 * (2^(1/3))^2
  -- (-12 * 2^(1/3)) * (4 * 2^(1/3)) = -48 * (2^(1/3))^2
  -- (-12 * 2^(1/3)) * 2 = -24 * 2^(1/3)
  -- -11 * (4 * 2^(1/3)) = -44 * 2^(1/3)
  -- -11 * 2 = -22
  -- Sum up all terms:
  -- 192 + (48 * (2^(1/3))^2 - 48 * (2^(1/3))^2) + (-24 * 2^(1/3) - 44 * 2^(1/3)) - 22
  -- The quadratic terms cancel.
  -- So total right side is: 192 - (68 * 2^(1/3)) - 22 = 170 - 68 * 2^(1/3)
  -- The left side after cross multiply is: 34 * (5 - 2 * 2^(1/3)) = 170 - 68 * 2^(1/3)
  -- So indeed equal.
  nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) ^ 2 - 1), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) ^ 2 - 2), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) ^ 2), h10]