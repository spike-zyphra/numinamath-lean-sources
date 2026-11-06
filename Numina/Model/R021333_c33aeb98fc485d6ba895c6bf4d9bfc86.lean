import Mathlib

theorem inequalities_326681 (x : ℝ) :
    abs (abs (x - 2) - 6) + abs (3 * x + 2) ≥ 8 ↔
    x ≥ 1 / 2 ∨ x ≤ -3 := by
  constructor
  · -- Assume abs (abs (x - 2) - 6) + abs (3 * x + 2) ≥ 8
    intro h
    -- Let's consider cases based on the value of x - 2
    by_cases h1 : 0 ≤ (x - 2)
    · -- If x - 2 ≥ 0, then abs (x - 2) = x - 2
      have h_abs1 : abs (x - 2) = x - 2 := by
        rw [abs_of_nonneg h1]
      rw [h_abs1] at h
      -- Now we analyze |x - 2 - 6| which is abs (x - 2 - 6)
      by_cases h2 : (x - 2) - 6 ≥ 0
      · -- Case where x - 2 ≥ 6, so abs (x - 2 - 6) = (x - 2 - 6)
        have h_abs2 : abs ((x - 2) - 6) = (x - 2) - 6 := by
          rw [abs_of_nonneg h2]
        rw [h_abs2] at h
        -- Now analyze the expression: (x - 2 - 6) + abs (3 * x + 2) ≥ 8
        -- Thus, abs (3 * x + 2) ≥ 8 + 6 - (x - 2) which expands to abs (3 * x + 2) ≥ 14 - (x - 2)
        by_cases h3 : 3 * x + 2 ≥ 0
        · -- If 3x + 2 ≥ 0, then abs (3x + 2) = 3x + 2
          have h_abs3 : abs (3 * x + 2) = 3 * x + 2 := by
            rw [abs_of_nonneg h3]
          rw [h_abs3] at h
          -- Solve the inequality: (x - 2 - 6) + (3x + 2) ≥ 8
          -- 4x - 6 ≥ 8
          -- 4x ≥ 14
          -- x ≥ 14/4 = 3.5
          -- So x ≥ 3.5 implies x ≥ 1/2
          left
          linarith
        · -- If 3x + 2 < 0, then abs (3x + 2) = -(3x + 2)
          have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
            rw [abs_of_neg (by linarith)]
          rw [h_abs3] at h
          -- Solve inequality: (x - 2 - 6) - (3x + 2) ≥ 8
          -- -2x - 10 ≥ 8
          -- -2x ≥ 18
          -- x ≤ -9
          -- So x ≤ -9 implies x ≤ -3
          right
          linarith
      · -- Case where 0 ≤ x - 2 < 6, so abs (x - 2 - 6) = 6 - (x - 2)
        have h_neg2 : (x - 2) - 6 < 0 := by linarith
        have h_abs2 : abs ((x - 2) - 6) = 6 - (x - 2) := by
          rw [abs_of_neg h_neg2]
          all_goals linarith
        rw [h_abs2] at h
        -- Now analyze: (6 - (x - 2)) + abs (3 * x + 2) ≥ 8
        -- Thus abs (3 * x + 2) ≥ 8 - (6 - (x - 2)) = 8 - 6 + (x - 2) = 2 + (x - 2) = x
        -- Now solve cases for 3x + 2
        by_cases h3 : 3 * x + 2 ≥ 0
        · -- If 3x + 2 ≥ 0
          have h_abs3 : abs (3 * x + 2) = 3 * x + 2 := by
            rw [abs_of_nonneg h3]
          rw [h_abs3] at h
          -- Solve inequality: (6 - (x - 2)) + (3x + 2) ≥ 8
          -- 6 - x + 2 + 3x + 2 ≥ 8
          -- 2x + 10 ≥ 8
          -- 2x ≥ -2
          -- x ≥ -1
          left
          linarith
          -- x ≥ -1 is satisfied by the case disjunction
        · -- If 3x + 2 < 0
          have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
            rw [abs_of_neg (by linarith)]
          rw [h_abs3] at h
          -- Solve inequality: (6 - (x - 2)) - (3x + 2) ≥ 8
          -- 6 - x + 2 - 3x - 2 ≥ 8
          -- -4x + 6 ≥ 8
          -- -4x ≥ 2
          -- x ≤ -0.5
          right
          -- Need to show x ≤ -3
          -- But resulting in x ≤ -0.5
          -- Contradicts: maybe need to re-examine
          nlinarith [abs_nonneg (x - 2), abs_nonneg (3 * x + 2)]
          -- Collectively analyze all inequalities to conclude
    · -- If x - 2 < 0, then abs (x - 2) = 2 - x
      have h_neg1 : (x - 2) < 0 := by linarith
      have h_abs1 : abs (x - 2) = 2 - x := by
        rw [abs_of_neg h_neg1]
        all_goals nlinarith
      rw [h_abs1] at h
      -- Now analyze abs ((2 - x) - 6) which is abs (2 - x - 6) = abs (-x - 4)
      by_cases h2 : (2 - x) - 6 ≥ 0
      · -- Case where (2 - x) ≥ 6, so x ≤ -4
        -- Then abs (-x - 4) = (-x - 4) * -1? No: abs (-x - 4) = |-x - 4| = |x + 4|
        have h_abs2 : abs ((2 - x) - 6) = (2 - x) - 6 := by
          rw [abs_of_nonneg h2]
        rw [h_abs2] at h
        -- Now analyze the expression: (2 - x - 6) + abs (3 * x + 2) ≥ 8
        -- Compute (2 - x - 6) = -4 - x
        by_cases h3 : 3 * x + 2 ≥ 0
        · -- If 3x + 2 ≥ 0
          have h_abs3 : abs (3 * x + 2) = 3 * x + 2 := by
            rw [abs_of_nonneg h3]
          rw [h_abs3] at h
          -- Solve inequality: (-4 - x) + (3x + 2) ≥ 8
          -- -4 - x + 3x + 2 ≥ 8
          -- 2x - 2 ≥ 8
          -- 2x ≥ 10
          -- x ≥ 5
          -- But when x ≥ 5, (2 - x) may not >= 0, but contradiction
          -- rethink: perhaps modulus math was wrong
          -- Looking at h_neg1: x - 2 < 0 or x < 2
          -- But need x ≤ -4 for h2 to be true
          nlinarith
        · -- If 3x + 2 < 0
          have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
            rw [abs_of_neg (by linarith)]
          rw [h_abs3] at h
          -- Solve inequality: (-4 - x) + (- (3x + 2)) ≥ 8
          -- -4 - x - 3x - 2 ≥ 8
          -- -4x - 6 ≥ 8
          -- -4x ≥ 14
          -- x ≤ -3.5
          -- Thus x ≤ -3.5 implies x ≤ -3
          right
          linarith
      · -- Case where x - 2 < 0 and (2 - x) - 6 < 0, so abs ((2 - x) - 6) = 6 - (2 - x)
        have h_neg2 : (2 - x) - 6 < 0 := by linarith
        have h_abs2 : abs ((2 - x) - 6) = 6 - (2 - x) := by
          rw [abs_of_neg h_neg2]
          all_goals linarith
        rw [h_abs2] at h
        -- Now the expression is: (6 - (2 - x)) + abs (3 * x + 2) ≥ 8
        -- Compute: 6 - 2 + x = 4 + x
        by_cases h3 : 3 * x + 2 ≥ 0
        · -- If 3x + 2 ≥ 0
          have h_abs3 : abs (3 * x + 2) = 3 * x + 2 := by
            rw [abs_of_nonneg h3]
          rw [h_abs3] at h
          -- Solve inequality: 4 + x + 3x + 2 ≥ 8
          -- 4 + x + 3x + 2 ≥ 8
          -- 4x + 6 ≥ 8
          -- 4x ≥ 2
          -- x ≥ 0.5
          left
          linarith
        · -- If 3x + 2 < 0
          have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
            rw [abs_of_neg (by linarith)]
          rw [h_abs3] at h
          -- Solve inequality: 4 + x - (3x + 2) ≥ 8
          -- 4 + x - 3x - 2 ≥ 8
          -- -2x + 2 ≥ 8
          -- -2x ≥ 6
          -- x ≤ -3
          right
          linarith
  · -- Assume x ≥ 1/2 ∨ x ≤ -3 prove abs (abs (x - 2) - 6) + abs (3 * x + 2) ≥ 8
    rintro (h | h)
    · -- Case x ≥ 1/2
      -- Now we need to show the inequality holds
      by_cases h1 : 0 ≤ (x - 2)
      · -- Case where x - 2 ≥ 0, so abs (x - 2) = x - 2
        have h_abs1 : abs (x - 2) = x - 2 := by
          rw [abs_of_nonneg h1]
        rw [h_abs1]
        by_cases h2 : (x - 2) - 6 ≥ 0
        · -- Case where x - 2 ≥ 6
          have h_abs2 : abs ((x - 2) - 6) = (x - 2) - 6 := by
            rw [abs_of_nonneg h2]
          rw [h_abs2]
          -- Since x ≥ 1/2, need to check abs (3 * x + 2)
          by_cases h3 : 3 * x + 2 ≥ 0
          · -- Case where 3x + 2 ≥ 0
            have h_abs3 : abs (3 * x + 2) = 3 * x + 2 := by
              rw [abs_of_nonneg h3]
            rw [h_abs3]
            linarith
          · -- Case where 3x + 2 < 0
            have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
              rw [abs_of_neg (by linarith)]
            rw [h_abs3]
            -- But this would not hold since x >= 1/2
            -- contradiction would be raised
            linarith
        · -- Case where 0 ≤ x - 2 < 6
          have h_neg2 : (x - 2) - 6 < 0 := by linarith
          have h_abs2 : abs ((x - 2) - 6) = 6 - (x - 2) := by
            rw [abs_of_neg h_neg2]
            all_goals linarith
          rw [h_abs2]
          -- Now analyze abs (3x + 2)
          by_cases h3 : 3 * x + 2 ≥ 0
          · -- Case where 3x + 2 ≥ 0
            have h_abs3 : abs (3 * x + 2) = 3 * x + 2 := by
              rw [abs_of_nonneg h3]
            rw [h_abs3]
            -- Solve inequality: 6 - (x - 2) + 3x + 2 >= 8
            -- Simplify: 6 - x + 2 + 3x + 2 >= 8
            -- Expanding to: 2x + 10 >= 8
            -- 2x >= -2
            -- x >= -1
            -- Given assumption x >=1/2, so true
            linarith
          · -- Case where 3x + 2 < 0
            have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
              rw [abs_of_neg (by linarith)]
            rw [h_abs3]
            nlinarith [h]
      · -- If x - 2 < 0, then abs (x - 2) = 2 - x
        have h_neg1 : (x - 2) < 0 := by linarith
        have h_abs1 : abs (x - 2) = 2 - x := by
          rw [abs_of_neg h_neg1]
          all_goals linarith
        rw [h_abs1]
        -- Now analyze abs ((2 - x) - 6)
        by_cases h2 : (2 - x) - 6 ≥ 0
        · -- Case where (2 - x) ≥ 6, so x <= -4
          have h_abs2 : abs ((2 - x) - 6) = (2 - x) - 6 := by
            rw [abs_of_nonneg h2]
          rw [h_abs2]
          -- Since x >=1/2 contradicts x <= -4
          -- would not work
          nlinarith
        · -- Case where x - 2 < 0 and (2 - x) - 6 < 0
          have h_neg2 : (2 - x) - 6 < 0 := by linarith
          have h_abs2 : abs ((2 - x) - 6) = 6 - (2 - x) := by
            rw [abs_of_neg h_neg2]
            all_goals linarith
          rw [h_abs2]
          -- Now analyze abs (3 * x + 2)
          by_cases h3 : 3 * x + 2 >= 0
          · -- Case where 3x + 2 >= 0
            have h_abs3 : abs (3 * x + 2) = 3 * x + 2 := by
              rw [abs_of_nonneg h3]
            rw [h_abs3]
            -- Solve inequality: 6 - (2 - x) + 3x + 2 >=8
            -- Compute: 6 -2 +x +3x +2 >=8
            -- i.e. 4x +6 >=8
            -- i.e. 4x >=2
            -- i.e. x >=0.5
            -- which matches x >=1/2
            linarith
          · -- Case where 3x + 2 < 0
            have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
              rw [abs_of_neg (by linarith)]
            rw [h_abs3]
            -- Solve inequality: 6 - (2 - x) - (3x + 2) >=8
            -- Compute:6 -2 +x -3x -2 >=8
            -- i.e. -2x +2 >=8
            -- i.e. -2x >=6
            -- i.e. x <=-3
            -- contradicts assumption x >=1/2
            linarith
    · -- Case x ≤ -3
      -- Now we need to show the inequality holds
      -- First analyze abs (x - 2): since x <= -3, x -2 <= -5 <0
      have h_neg1 : (x - 2) <= -3 -2 := by linarith
      have h_neg2 : (x - 2) < 0 := by linarith
      have h_abs1 : abs (x - 2) = 2 - x := by
        rw [abs_of_neg h_neg2]
        all_goals linarith
      rw [h_abs1]
      -- Now analyze abs ((2 - x) - 6)
      have h2 : (2 - x) - 6 >=3-6+3-6 := by nlinarith
      -- But since x <= -3, 2 - x >=5
      -- So (2 - x) -6 >=-1
      -- if (2 - x) >=6, then abs((-x-4))=6-0=(something)
      -- h_abs2: from computation
      by_cases h3 : (2 - x) - 6 >=0
      · -- Case where (2 - x) >=6
        have h_abs2 : abs ((2 - x) - 6) = (2 - x) - 6 := by
          rw [abs_of_nonneg h3]
        rw [h_abs2]
        -- Now analyze abs (3x + 2): since x <= -3, 3x+2 <=-9+2=-7<0
        have h_neg3 : 3 * x + 2 <0 := by linarith
        have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
          rw [abs_of_neg h_neg3]
        rw [h_abs3]
        -- Solve inequality: ((2 - x) - 6) + (- (3x + 2)) >=8
        -- (-x -4) - (3x +2) = (-x -4) + (-3x -2)
        -- = -4x -6 >=8
        -- -4x >=14
        -- x <=-3.5
        -- x <=-3.5 implies x <=-3
        linarith
      · -- Case where (2 - x) <6
        have h_neg3 : (2 - x) - 6 <0 := by linarith
        have h_abs2 : abs ((2 - x) - 6) = 6 - (2 - x) := by
          rw [abs_of_neg h_neg3]
          all_goals linarith
        rw [h_abs2]
        -- Now analyze abs (3x + 2)
        have h_neg4 : 3 * x + 2 <0 := by linarith
        have h_abs3 : abs (3 * x + 2) = -(3 * x + 2) := by
          rw [abs_of_neg h_neg4]
        rw [h_abs3]
        -- Solve inequality:6 - (2 - x) + (- (3x + 2)) >=8
        -- (6 -2 +x) + (-3x -2) >=8
        -- (4 +x) + (-3x -2) >=8
        -- (-2x +2) >=8
        -- -2x >=6
        -- x <=-3
        linarith