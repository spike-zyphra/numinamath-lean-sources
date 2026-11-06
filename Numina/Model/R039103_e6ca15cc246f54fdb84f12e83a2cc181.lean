import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8166 :
  IsLeast {x | ∃ a b c : ℝ, a ∈ Icc 1 3 ∧ b ∈ Icc 1 3 ∧ c ∈ Icc 1 3 ∧ max (max a b) c ≥ 2 ∧ a + b + c = 5 ∧ x = a^2 + b^2 + c^2} (17/2) := by
  constructor
  · -- We need to show 17/2 is in the set
    use 2
    use 3 / 2
    use 3 / 2
    constructor
    · -- Show that 2 ∈ [1, 3]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 3/2 ∈ [1, 3]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 3/2 ∈ [1, 3]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that max (max 2 3/2) 3/2 ≥ 2
      norm_num [max_assoc, max_comm, max_left_comm]
    constructor
    · -- Show that 2 + 3/2 + 3/2 = 5
      norm_num
    · -- Show that 17/2 = 2^2 + (3/2)^2 + (3/2)^2
      norm_num
  · -- We need to show any x in the set is ≥ 17/2
    rintro x ⟨a, b, c, ha, hb, hc, hmax, hsum1, hx⟩ 
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    by_contra h
    push_neg at h
    have h11 : a ≤ 3 := by linarith
    have h12 : b ≤ 3 := by linarith
    have h13 : c ≤ 3 := by linarith
    -- Here we can need to split the cases as to which variable is the max
    by_cases h1 : a ≥ 2
    · -- Assume that a >= 2
      -- Then the sum b + c = 5 - a is given
      -- Then b and c's max is needed
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 3 / 2)]
    · -- Assume that a < 2
      by_cases h2 : b ≥ 2
      · -- Assume that b >= 2
        -- Then a < 2 and b >= 2
        -- Then a < 2 and b >= 2 need to find the minimum
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 2), sq_nonneg (c - 3 / 2)]
      · -- Assume that b < 2
        by_cases h3 : c ≥ 2
        · -- Assume that c >= 2
          -- Then a < 2, b < 2 and c >= 2
          -- Then the minimum
          nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 2)]
        · -- Assume that c < 2
          -- Then all variables < 2, and none in right half
          -- But this contradicts max >= 2
          -- Then max is none at right
          -- Contradiction occurs
          -- Goal requires contradiction
          exfalso 
          have h4 : max (max a b) c < 2 := by 
            have h11 : a < 2 := by 
              linarith
            have h12 : b < 2 := by
              linarith
            have h13 : c < 2 := by
              linarith
            simp [max_lt_iff, h11, h12, h13]
            all_goals
              try { norm_num }
          linarith
          all_goals tauto
          all_goals tauto 
          all_goals tauto
          all_goals tauto
          all_goals tauto
          all_goals tauto
          all_goals tauto
          all_goals tauto