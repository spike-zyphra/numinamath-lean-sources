import Mathlib
/-6. (BUL 6) Solve the system  $$ \begin{aligned} |x+y|+|1-x| & =6 \\ |x+y+1|+|1-y| & =4 \end{aligned} $$-/
open Real
theorem other_24751 (x y : ℝ)
(h1 : |x + y|+ |1 - x| = 6)
(h2 : |x + y + 1| + |1 - y| = 4) :
(x = -2 ∧ y = -1) ∨ (x = -14 / 3 ∧ y = 13 / 3) := by
  -- Introduce substitution u = x + y
  let u := x + y
  have hu : u = x + y := rfl

  -- Transform equations in terms of u
  have eq1 : |u| + |1 - x| = 6 := by rw [← hu] at h1; exact h1
  have eq2 : |u + 1| + |1 - y| = 4 := by rw [← hu] at h2; exact h2

  -- Express y in terms of u and x
  have hy : y = u - x := by
    rw [hu]
    linarith

  -- Substitute y in the second equation
  have eq2' : |u + 1| + |1 - u + x| = 4 := by
    rw [hy] at eq2
    have h3 : 1 - (u - x) = 1 - u + x := by ring
    rw [h3] at eq2
    linarith

  -- Main case analysis based on u ≤ -1
  by_cases hu1 : u ≤ -1
  · -- Case 1: u ≤ -1
    by_cases x1 : x ≤ 1
    · -- Subcase 1.1: u ≤ -1 and x ≤ 1
      -- Handle absolute values based on sign conditions
      have h1 : abs u = -u := by rw [abs_of_nonpos (show u ≤ 0 by linarith)]
      have h2 : abs (1 - x) = 1 - x := by rw [abs_of_nonneg (show 1 - x ≥ 0 by linarith)]
      have h3 : abs (u + 1) = -(u + 1) := by rw [abs_of_nonpos (show u + 1 ≤ 0 by linarith)]
      rw [h1, h2] at eq1
      rw [h3] at eq2'

      -- Derive key equation
      have eq1' : x + u = -5 := by linarith

      -- Further case analysis based on 1 - u + x ≥ 0
      by_cases h : 1 - u + x ≥ 0
      · -- When 1 - u + x ≥ 0, find first solution (-2,-1)
        have h4 : abs (1 - u + x) = 1 - u + x := by rw [abs_of_nonneg h]
        rw [h4] at eq2'
        have eq2 : x - 2 * u = 4 := by linarith
        have hu2 : u = -3 := by linarith [eq1', eq2]
        have hx : x = -2 := by linarith [eq1', hu2]
        have hy : y = -1 := by linarith [hu, hx, hu2]
        left
        exact ⟨hx, hy⟩
      · -- When 1 - u + x < 0, leads to contradiction
        have h4 : abs (1 - u + x) = -(1 - u + x) := by rw [abs_of_neg (lt_of_not_ge h)]
        rw [h4] at eq2'
        have eq2 : x = -6 := by linarith
        have hu2 : u = 1 := by linarith [eq1', eq2]
        linarith

    · -- Subcase 1.2: u ≤ -1 and x > 1
      -- Handle absolute values based on sign conditions
      rw [hu] at eq1 eq2'
      have h1 : 1 - (x + y) + x = 1 - y := by ring
      rw [h1] at eq2'
      have h2 : abs (x + y) = -(x + y) := by
        rw [abs_of_nonpos]
        linarith
      have h3 : x > 1 := by
        by_contra h
        push_neg at h
        have h4 : x ≤ 1 := by linarith
        exact x1 h4
      have h4 : abs (1 - x) = x - 1 := by
        have h5 : 1 - x < 0 := by linarith
        rw [abs_of_neg h5]
        linarith
      rw [h2, h4] at eq1
      have h5 : -(x + y) + (x - 1) = 6 := by
        linarith
      have hy : y = -7 := by
        nlinarith
      have h6 : abs (1 - y) = 8 := by
        rw [hy]
        norm_num [abs_of_pos]
      have h7 : abs (x + y + 1) + 8 = 4 := by
        have h8 : abs (x + y + 1) + abs (1 - y) = 4 := by linarith [eq2']
        rw [h6] at h8
        linarith
      have h8 : abs (x + y + 1) ≤ 0 := by linarith [h7]
      have h9 : abs (x + y + 1) ≥ 0 := abs_nonneg (x + y + 1)
      have h10 : abs (x + y + 1) = 0 := by linarith [h8, h9]
      have h11 : x + y + 1 = 0 := abs_eq_zero.mp h10
      rw [hy] at h11
      nlinarith

  · -- Case 2: u > -1
    -- Further case analysis based on u ≤ 0
    by_cases hu2 : u ≤ 0
    · -- Subcase 2.1: -1 < u ≤ 0
      by_cases x1 : x ≤ 1
      · -- When x ≤ 1, find second solution (-14/3,13/3)
        have hu3 : u > -1 := by linarith
        have h11 : abs u = -u := by
          rw [abs_of_nonpos (show u ≤ 0 by linarith)]
        have h12 : abs (1 - x) = 1 - x := by
          rw [abs_of_nonneg (show 1 - x ≥ 0 by linarith)]
        rw [h11, h12] at eq1
        have h3 : x + u = -5 := by linarith
        have hy : y = -5 - 2 * x := by
          linarith [hu, h3]
        have h4 : abs (u + 1) = u + 1 := by
          rw [abs_of_pos (show u + 1 > 0 by linarith [show u > -1 by linarith]) ]
        have h5 : abs (1 - u + x) = abs (2 * x + 6) := by
          have h6 : 1 - u + x = 2 * x + 6 := by
            linarith [hu, h3]
          rw [h6]
        rw [h4, h5] at eq2'
        have hu_eq : u = -5 - x := by linarith [h3]
        rw [hu_eq] at eq2'
        by_cases h7 : 2 * x + 6 ≥ 0
        · rw [abs_of_nonneg h7] at eq2'
          nlinarith
        · rw [abs_of_neg (lt_of_not_ge h7)] at eq2'
          have hx1 : x = -14 / 3 := by
            nlinarith
          have hy1 : y = 13 / 3 := by
            rw [hx1] at hy
            linarith
          right
          constructor <;> linarith
      · -- When x > 1, leads to contradiction
        have h1 : 1 - x < 0 := by
          by_contra h
          push_neg at h
          have h3 : x ≤ 1 := by linarith
          have h3 : x ≤ 1 := by linarith
          exact x1 (show x ≤ 1 by linarith)
        have h1' : abs (1 - x) = x - 1 := by
          rw [abs_of_neg (show 1 - x < 0 by linarith)]
          linarith
        have h2 : abs u = -u := by
          have h3 : u ≥ -1 := by
            by_contra h
            push_neg at h
            have h4 : u ≤ -1 := by linarith
            exact hu1 (show u ≤ -1 by linarith)
          rw [abs_of_nonpos (show u ≤ 0 by linarith)]
        have hu' : u = x + y := by linarith
        rw [h2, h1'] at eq1
        have h3 : y = -7 := by
          linarith [hu']
        have h4 : u = x + y := by linarith
        rw [show u = x + y by linarith [hu], h3] at eq2'
        have h5 : abs (1 - (x + (-7)) + x) = 8 := by
          have h6 : 1 - (x + (-7)) + x = 8 := by
            linarith
          rw [h6]
          norm_num
        rw [h5] at eq2'
        have h7 : abs (x + (-7) + 1) + 8 = 4 := by linarith
        have h8 : abs (x + (-7) + 1) = -4 := by linarith
        have h9 : abs (x + (-7) + 1) ≥ 0 := abs_nonneg (x + (-7) + 1)
        linarith
    · -- Subcase 2.2: u > 0
      -- Leads to contradiction
      by_cases x1 : x ≤ 1
      · have hu_pos : u > 0 := by
          by_contra h
          push_neg at h
          have h1 : u ≤ 0 := by linarith
          contradiction
        have h1 : abs u = u := abs_of_pos hu_pos
        have h2 : 1 - x ≥ 0 := by linarith
        have h3 : abs (1 - x) = 1 - x := abs_of_nonneg h2
        rw [h1, h3] at eq1
        have h4 : abs (u + 1) = u + 1 := by
          have h5 : u + 1 > 0 := by linarith
          rw [abs_of_pos h5]
        have h6 : abs (1 - u + x) = abs (1 - u + x) := by rfl
        rw [h4] at eq2'
        have h7 : x = 1 - (6 - u) := by linarith
        have h8 : x = u - 5 := by linarith
        have h9 : u ≤ 6 := by linarith [x1, h8]
        have h10 : 1 - u + x = -4 := by
          rw [h8]
          linarith
        have h11 : abs (1 - u + x) = 4 := by
          rw [h10]
          norm_num [abs_of_nonneg, abs_of_neg]
        rw [h11] at eq2'
        have h12 : u + 1 = 0 := by linarith
        have h13 : u = -1 := by linarith
        linarith [hu_pos, h13]
      · have hu2' : u > 0 := by
          simpa using hu2
        have hx1' : x > 1 := by
          simpa using x1
        have h1 : abs u = u := by
          rw [abs_of_pos]
          linarith
        have h2 : abs (1 - x) = abs (x - 1) := by
          rw [show 1 - x = -(x - 1) by ring]
          rw [abs_neg]
        have h3 : abs (x - 1) = x - 1 := by
          rw [abs_of_pos]
          linarith [show x - 1 > 0 from by linarith [hx1']]
        have eq1' : abs u + abs (1 - x) = 6 := eq1
        rw [h1, h2, h3] at eq1'
        have h4 : u + (x - 1) = 6 := by linarith
        have h5 : u + x = 7 := by linarith
        have h7 : abs (u + 1) = u + 1 := by
          rw [abs_of_pos]
          linarith [show u + 1 > 0 from by linarith [hu2']]
        have eq2 : abs (u + 1) + abs (1 - u + x) = 4 := by
          linarith [eq2']
        rw [h7] at eq2
        have h8 : abs (1 - u + x) = 3 - u := by linarith
        have h9 : 1 - u + x = 8 - 2 * u := by
          have hx : x = 7 - u := by linarith [h5]
          rw [hx]
          linarith
        rw [h9] at h8
        by_cases h : 8 - 2 * u ≥ 0
        · rw [abs_of_nonneg h] at h8
          have hu5 : u = 5 := by linarith
          linarith [show u ≤ 4 from by linarith [h], hu5]
        · rw [abs_of_neg (lt_of_not_ge h)] at h8
          have hu11 : u = 11 / 3 := by linarith
          nlinarith [show 8 - 2 * u < 0 from by linarith [hu11]]
