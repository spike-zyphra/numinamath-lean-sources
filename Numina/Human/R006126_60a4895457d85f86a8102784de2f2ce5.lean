import Mathlib


-- Given real numbers a, b, c that satisfy the equations a + b + c = 2 and abc = 4: Determine the minimum value of max(a, b, c).

lemma lemma1 : ∀ (a b c:ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → (a + b + c)^3 ≥ 27* (a*b*c) := by
intro a b c h
rcases h with ⟨ha, hb , hc⟩
-- Use nonlinear arithmetic with squared differences to establish AM-GM
nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b + c - 3 * a), sq_nonneg (a + b + c - 3 * b), sq_nonneg (a + b + c - 3 * c),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]

-- Main theorem: The minimum value of max(a,b,c) is 4
-- We assume a ≥ b ≥ c without loss of generality, so max(a,b,c) = a
theorem algebra_618455 : IsLeast {x | ∃ a b c : ℝ, (a ≥ b ∧ b ≥ c) ∧ x = a ∧ a + b + c = 2 ∧ a * b * c = 4} 4 := by
constructor

-- Part 1: Show that 4 is achievable (witness: a=4, b=-1, c=-1)
· simp
  use 4, -1, -1  -- The triple (4, -1, -1) satisfies all conditions
  norm_num       -- Verify: 4 ≥ -1 ≥ -1, 4 + (-1) + (-1) = 2, 4·(-1)·(-1) = 4

-- Part 2: Show that 4 is a lower bound (no valid triple gives a < 4)
· unfold lowerBounds
  simp
  intro k a b c hge1 hge2 hk hadd hmul
  -- We need to prove k ≥ 4, where k = a and constraints are satisfied

  -- Case analysis based on the sign of c
  by_cases hpos : c ≥ 0

  -- Case 1: All numbers are non-negative (c ≥ 0, hence b ≥ 0, a ≥ 0)
  · have : (a + b + c)^3 ≥ 27 * (a*b*c) := by
      apply lemma1  -- Apply AM-GM inequality
      constructor
      · linarith    -- a ≥ b ≥ c ≥ 0 implies a ≥ 0
      · constructor
        · linarith  -- b ≥ c ≥ 0 implies b ≥ 0
        · linarith  -- c ≥ 0 by assumption
    -- Substitute constraints: (2)³ ≥ 27·4, so 8 ≥ 108, contradiction!
    rw [hadd, hmul] at this
    linarith  -- This case is impossible

  -- Case 2: c < 0, further subdivided
  · by_cases hneg1 : c > -1 ∧ c < 0

    -- Subcase 2a: -1 < c < 0
    · by_cases b ≥ 0
      -- If b ≥ 0 and c < 0, then abc ≤ 0, contradicting abc = 4 > 0
      · have : a * b * c ≤ 0 := by
          refine mul_nonpos_of_nonneg_of_nonpos ?ha ?hb
          nlinarith  -- a ≥ b ≥ 0 implies a ≥ 0
          linarith   -- c < 0
        linarith     -- Contradiction with abc = 4 > 0

      -- If b < 0 and -1 < c < 0, then 0 < bc < 1
      · have hlt : b * c < 1 ∧ b * c > 0:= by
          constructor
          · nlinarith  -- Both b, c negative and |c| < 1 implies bc < 1
          · nlinarith  -- Both b, c negative implies bc > 0
        rw [mul_assoc] at hmul  -- Rewrite abc = a(bc) = 4
        have : a > 4 := by nlinarith  -- Since bc < 1, we need a > 4
        linarith  -- Therefore k = a > 4, so k ≥ 4

    -- Subcase 2b: c ≤ -1
    · by_cases hneg2 : c < -1

      -- If c < -1
      · by_cases hpos : b ≥ 0
        -- Similar argument: if b ≥ 0, c < 0, then abc ≤ 0, contradiction
        · have : a * b * c ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos
            nlinarith  -- a ≥ b ≥ 0 implies a ≥ 0
            linarith   -- c < -1 < 0
          linarith     -- Contradiction with abc = 4

        -- If b < 0 and c < -1
        · by_cases hneg : b > -1
          -- If -1 < b < 0 and c < -1, derive contradiction
          · rw [hk]
            by_contra ha  -- Assume a < 4, derive contradiction
            have h1 : b + c > -2 := by nlinarith  -- Since b > -1
            have h2 : b * c < 1 := by nlinarith   -- Product bound
            -- Use discriminant argument: (b-c)² < 0, which is impossible
            have : (b-c)^2 < 0 := by
              calc
                _ = (b+c)^2 - 4 *(b*c) := by ring
                _ < _ := by nlinarith
            have : (b-c)^2 ≥ 0 := by exact sq_nonneg (b - c)
            linarith  -- Contradiction

          -- If b ≤ -1 and c < -1, then b + c < -2, so a > 4
          · simp at hpos
            simp at hneg
            have : b + c < -2 := by linarith
            have : a > 4 := by linarith  -- From a + b + c = 2
            linarith  -- So k = a > 4

      -- If c = -1 (the boundary case)
      · have : c = -1 := by
          simp at hneg1  -- hneg1 is false: not(-1 < c < 0)
          simp at hneg2  -- hneg2 is false: not(c < -1)
          -- Therefore c = -1 by trichotomy
          by_contra h
          have : c > -1 := by exact lt_of_le_of_ne hneg2 fun a => h (id (Eq.symm a))
          have := hneg1 this
          linarith

        -- Substitute c = -1 into constraints
        rw [this] at hadd
        rw [this] at hmul

        -- From a + b + (-1) = 2, we get a + b = 3
        have hadd' : a + b = 3 := by
          calc
            _ = a + b + (-1) + 1 := by ring
            _ = _ := by rw [hadd]; ring

        -- From ab(-1) = 4, we get ab = -4
        have hmul' : a * b = -4 := by
          calc
            _ = a * b * (-1) * (-1) := by simp
            _ = _ := by rw [hmul]; ring

        -- Solve the system: a + b = 3, ab = -4
        -- Using (a-b)² = (a+b)² - 4ab = 9 - 4(-4) = 25
        have : (a - b)^2 = 25 := by
          calc
            _ = (a+b)^2 - 4 * (a*b) := by ring
            _ = _ := by rw [hadd', hmul']; ring

        -- Since a ≥ b, we have a - b = 5
        have : a - b = 5 := by nlinarith

        -- Solving: a = 4, b = -1
        have : a = 4 := by linarith
        have : b = -1 := by linarith

        -- Therefore k = a = 4
        rw [hk]
        linarith
