import Mathlib

/- Given the equation 15xy - 35x - 6y = 3 over integers, 
prove that the only solution is (x, y) = (-3, 2)-/
theorem algebra_100939 (x y : ℤ) (h : 15 * x * y - 35 * x - 6 * y = 3) :
    (x, y) = (-3, 2) := by

  -- Step 1: Transform the expression into factored form
  -- 15xy - 35x - 6y = 3 becomes (5x - 2)(3y - 7) = 17
  have h1 : (5 * x - 2) * (3 * y - 7) = 17 := by
    linarith

  -- Step 2: Since (5x - 2)(3y - 7) = 17, and 17 is prime,
  -- the possible integer values for (5x - 2) are ±1, ±17
  have h2 : 5 * x - 2 = 1 ∨ 5 * x - 2 = -1 ∨ 5 * x - 2 = 17 ∨ 5 * x - 2 = -17 := by
    have h2 : (5 * x - 2) * (3 * y - 7) = 17 := h1

    -- Any integer dividing 17 must be ±1 or ±17
    have h4 : (5 * x - 2) ∣ 17 := by
      exact Dvd.intro (3 * y - 7) h2

    -- Bound the possible values of (5x - 2) by using the fact that it divides 17
    have h5 : (5 * x - 2) ≤ 17 := by apply Int.le_of_dvd (by norm_num) h4

    -- Prove that (5x - 2) is also ≥ -17
    have h6 : (5 * x - 2) ≥ -17 := by
      by_cases h7 : (5 * x - 2) ≥ 0
      · -- Case: (5x - 2) ≥ 0, so it's already bounded above and below
        nlinarith [h5]
      · -- Case: (5x - 2) < 0, use negative divisibility
        have h10 : (- (5 * x - 2)) ∣ 17 := Int.neg_dvd.2 h4
        have h11 : (- (5 * x - 2)) ≤ 17 := Int.le_of_dvd (by norm_num) h10
        linarith

    -- Use interval_cases to deduce the only possible values in [-17, 17] that divide 17
    have h7 : (5 * x - 2) = 1 ∨ (5 * x - 2) = -1 ∨ (5 * x - 2) = 17 ∨ (5 * x - 2) = -17 := by
      interval_cases (5 * x - 2) <;> tauto

    exact h7

  -- Step 3: Go through all 4 possible values for (5x - 2) and solve for (x, y)

  -- Case 1: 5x - 2 = 1
  cases h2 with
  | inl h2l =>
    omega  -- No integer solution for x and y in this case

  | inr h2r =>
    -- Case 2: 5x - 2 = -1
    cases h2r with
    | inl h2rl =>
      omega  -- Again, no integer solution

    | inr h2rr =>
      -- Case 3: 5x - 2 = 17
      cases h2rr with
      | inl h2rrl =>
        omega  -- No integer solution

      | inr h2rrr =>
        -- Case 4: 5x - 2 = -17 → Solve for x
        have hx : x = -3 := by linarith

        -- Plug back into the original factored form to solve for y
        have hy : y = 2 := by
          have h3 : (5 * x - 2) * (3 * y - 7) = 17 := h1
          rw [h2rrr] at h3
          linarith

        -- Conclude the proof by showing the only solution is (x, y) = (-3, 2)
        exact Prod.ext hx hy
