import Mathlib

/- 8.42 Find the integers $x$, satisfying the inequality $\left|\frac{2}{x-13}\right|>\frac{8}{9}$ -/
theorem inequalities_180276 (x : ℤ) (hx : x ≠ 13) : |(2 / (x - 13 : ℝ))| > 8 / 9 ↔ x = 11 ∨ x = 12 ∨ x = 14 ∨ x = 15 := by
  -- We'll prove both directions of the equivalence
  constructor
  · -- Forward direction: Assume |2 / (x - 13)| > 8 / 9, show x = 11 ∨ x = 12 ∨ x = 14 ∨ x = 15
    intro h
    -- First, we verify that x - 13 ≠ 0, which is already given by the hypothesis hx
    have h1 : (x - 13 : ℝ) ≠ 0 := by
      intro h2
      have h2' : (x : ℝ) = 13 := by linarith
      have h2'' : x = 13 := by exact_mod_cast h2'
      contradiction
    -- The absolute value inequality means either 2/(x-13) > 8/9 or 2/(x-13) < -8/9
    have h2 : (2 / (x - 13 : ℝ)) > 8 / 9 ∨ (2 / (x - 13 : ℝ)) < -8 / 9 := by
      cases' abs_cases (2 / (x - 13 : ℝ)) with h3 h3
      · -- Case where 2 / (x - 13) ≥ 0
        left
        linarith
      · -- Case where 2 / (x - 13) < 0
        right
        linarith
    -- We analyze each case separately
    cases' h2 with h4 h5
    · -- Case 1: 2 / (x - 13) > 8 / 9
      -- We need to determine whether x - 13 is positive or negative
      have h6 : (x - 13 : ℝ) > 0 ∨ (x - 13 : ℝ) < 0 := by
        by_contra h7
        push_neg at h7
        have h8 : (x - 13 : ℝ) = 0 := by linarith
        contradiction
      cases' h6 with h7 h8
      · -- Subcase: (x - 13) > 0, which means x > 13
        -- Multiply both sides of the inequality by (x - 13)
        have h10 : (2 : ℝ) > (8 / 9) * (x - 13) := by
          have h11 : (x - 13 : ℝ) > 0 := by linarith
          have h12 : (2 / (x - 13 : ℝ)) > (8 / 9 : ℝ) := by linarith
          have h13 : (2 : ℝ) > (8 / 9) * (x - 13) := by
            apply (lt_div_iff₀' h11).mp at h12
            linarith
          linarith
        -- Establish an upper bound for x
        have h15 : x ≤ 15 := by
          by_contra h16
          push_neg at h16
          have h17 : (x : ℝ) ≥ 16 := by exact_mod_cast h16
          nlinarith
        -- Establish a lower bound for x
        have h16 : x ≥ 14 := by
          by_contra h17
          push_neg at h17
          have h18 : x ≤ 13 := by linarith
          have h19 : (x : ℝ) ≤ (13 : ℝ) := by exact_mod_cast h18
          nlinarith
        -- With 14 ≤ x ≤ 15 and x being an integer, x must be either 14 or 15
        have h17 : x = 14 ∨ x = 15 := by
          omega
        cases' h17 with h18 h19
        · -- x = 14
          right
          right
          left
          exact h18
        · -- x = 15
          right
          right
          right
          exact h19
      · -- Subcase: (x - 13) < 0, which means x < 13
        have h9 : (x : ℝ) < 13 := by linarith
        -- Multiply both sides of the inequality by (x - 13), which reverses the inequality since x - 13 < 0
        have h10 : (2 : ℝ) < (8 / 9) * (x - 13) := by
          have h11 : (x - 13 : ℝ) < 0 := by linarith
          have h12 : (2 / (x - 13 : ℝ)) > (8 / 9 : ℝ) := by linarith
          have h13 : (2 : ℝ) < (8 / 9) * (x - 13) := by
            apply (lt_div_iff_of_neg' h11).mp at h12
            linarith
          linarith
        -- This leads to a contradiction because we get x ≥ 16 and x < 13
        have h15 : (x : ℝ) ≥ 16 := by
          by_contra h16
          push_neg at h16
          nlinarith
        have h16 : x ≥ 16 := by
          exact_mod_cast h15
        have h17 : x < 13 := by
          exact_mod_cast h9
        omega
    · -- Case 2: 2 / (x - 13) < -8 / 9
      -- Again, we need to determine whether x - 13 is positive or negative
      have h6 : (x - 13 : ℝ) > 0 ∨ (x - 13 : ℝ) < 0 := by
        by_contra h7
        push_neg at h7
        have h8 : (x - 13 : ℝ) = 0 := by linarith
        contradiction
      cases' h6 with h7 h8
      · -- Subcase: (x - 13) > 0, which means x > 13
        -- Multiply both sides of the inequality by (x - 13)
        have h10 : (2 : ℝ) < -(8 / 9) * (x - 13) := by
          have h11 : (x - 13 : ℝ) > 0 := by linarith
          have h12 : (2 / (x - 13 : ℝ)) < -(8 / 9 : ℝ) := by linarith
          have h13 : (2 : ℝ) < -(8 / 9) * (x - 13) := by
            apply (div_lt_iff₀' h11).mp at h12
            linarith
          linarith
        -- This leads to a contradiction because we get x ≤ 10 and x ≥ 14
        have h16 : x ≤ 10 := by
          by_contra h17
          push_neg at h17
          nlinarith
        have h17 : x ≥ 14 := by
          by_contra h18
          push_neg at h18
          nlinarith
        omega
      · -- Subcase: (x - 13) < 0, which means x < 13
        have h9 : (x : ℝ) < 13 := by linarith
        -- Multiply both sides of the inequality by (x - 13), which reverses the inequality since x - 13 < 0
        have h10 : (2 : ℝ) > -(8 / 9) * (x - 13) := by
          have h11 : (x - 13 : ℝ) < 0 := by linarith
          have h12 : (2 / (x - 13 : ℝ)) < -(8 / 9 : ℝ) := by linarith
          have h13 : (2 : ℝ) > -(8 / 9) * (x - 13) := by
            apply (div_lt_iff_of_neg' h11).mp at h12
            linarith
          linarith
        -- Establish a lower bound for x
        have h15 : x ≥ 11 := by
          by_contra h16
          push_neg at h16
          have h17 : x ≤ 10 := by linarith
          have h18 : (x : ℝ) ≤ (10 : ℝ) := by exact_mod_cast h17
          nlinarith
        -- Establish an upper bound for x
        have h16 : x < 13 := by
          exact_mod_cast h9
        -- With 11 ≤ x < 13 and x being an integer, x must be either 11 or 12
        have h17 : x = 11 ∨ x = 12 := by
          omega
        cases' h17 with h18 h19
        · -- x = 11
          left
          exact h18
        · -- x = 12
          right
          left
          exact h19
  · -- Backward direction: Assume x = 11 ∨ x = 12 ∨ x = 14 ∨ x = 15, prove |2 / (x - 13)| > 8 / 9
    -- We check each possible value of x
    rintro (h | h | h | h)
    · -- x = 11
      rw [h]
      norm_num
    · -- x = 12
      rw [h]
      norm_num
    · -- x = 14
      rw [h]
      norm_num
    · -- x = 15
      rw [h]
      norm_num
