import Mathlib
/- [Example 4.3.1] Find all quadruples $\left(x_{1}, x_{2}, x_{3}, x_{4}\right)$ such that the sum of any one of the numbers and the product of the other three numbers is equal to 2. -/
theorem algebra_275202 : {(x1, x2, x3, x4) : ℝ × ℝ × ℝ × ℝ | x1 + x2 * x3 * x4 = 2 ∧ x2 + x1 * x3 * x4 = 2 ∧ x3 + x1 * x2 * x4 = 2 ∧ x4 + x1 * x2 * x3 = 2} = {(1, 1, 1, 1), (3, -1, -1, -1), (-1, 3, -1, -1), (-1, -1, 3, -1), (-1, -1, -1, 3)}:= by
  -- Use extensionality to prove set equality by showing membership equivalence
  ext ⟨x1, x2, x3, x4⟩
  constructor
  .
    -- Forward direction: if (x1,x2,x3,x4) satisfies the system, then it's one of the 5 solutions
    intro h
    simp at h
    -- Extract the four equations from the hypothesis
    rcases h with ⟨h1, h2, h3, h4⟩
    -- Case analysis: check if all variables are equal
    by_cases h : x1 = x2 ∧ x2 = x3 ∧ x3 = x4
    .
      -- Case 1: All variables are equal
      rcases h with ⟨g1, g2, g3⟩
      subst x1 x2 x3
      -- Substitute and simplify to get a polynomial equation in x4
      replace h1 : (x4 - 1) * ((2 * x4 + 1) ^ 2 + 7) = 0:= by linarith
      simp at h1
      rcases h1 with h1 | h1
      .
        -- If x4 - 1 = 0, then x4 = 1, giving solution (1,1,1,1)
        replace h1 : x4 = 1:= by linarith
        subst x4
        simp
      .
        -- The second factor is always positive, so this case is impossible
        have g1 : (2 * x4 + 1) ^ 2 + 7 > 0:= by positivity
        linarith
    .
      -- Case 2: Not all variables are equal
      -- First prove that the product x1*x2*x3*x4 ≠ 0
      have h5 : x1 * x2 * x3 * x4 ≠ 0:= by
        by_contra H
        simp at H
        -- If any variable is 0, we get a contradiction with the original equations
        rcases H with ⟨⟨H | H⟩ | H⟩ | H
        all_goals
          subst H
          simp at h1 h2 h3 h4
        .
          -- Case x1 = 0
          subst x2 x3 x4
          norm_num at h1
        .
          -- Case x2 = 0
          subst x1 x3 x4
          norm_num at h2
        .
          -- Case x3 = 0
          subst x1 x2 x4
          norm_num at h3
        .
          -- Case x4 = 0
          subst x1 x2 x3
          norm_num at h4
      -- Define p as the product of all four variables
      set p:= x1 * x2 * x3 * x4 with hp
      clear_value p
      -- Multiply each equation by the corresponding variable
      replace h1 : x1 * (x1 + x2 * x3 * x4) = x1 * 2:= by rw [h1]
      replace h2 : x2 * (x2 + x1 * x3 * x4) = x2 * 2:= by rw [h2]
      replace h3 : x3 * (x3 + x1 * x2 * x4) = x3 * 2:= by rw [h3]
      replace h4 : x4 * (x4 + x1 * x2 * x3) = x4 * 2:= by rw [h4]
      -- Prove that 1 - p ≥ 0 using the constraint that (x1-1)² ≥ 0
      have g1 : 1 - p ≥ 0:= by
        replace h1 : 1 - p = (x1 - 1) ^ 2:= by linarith
        rw [h1]
        positivity
      -- Transform equations to show each variable satisfies a quadratic
      replace h1 : (x1 - 1 - √(1 - p)) * (x1 - 1 + √(1 - p)) = 0:= by
        ring_nf
        field_simp
        linarith
      replace h2 : (x2 - 1 - √(1 - p)) * (x2 - 1 + √(1 - p)) = 0:= by
        ring_nf
        field_simp
        linarith
      replace h3 : (x3 - 1 - √(1 - p)) * (x3 - 1 + √(1 - p)) = 0:= by
        ring_nf
        field_simp
        linarith
      replace h4 : (x4 - 1 - √(1 - p)) * (x4 - 1 + √(1 - p)) = 0:= by
        ring_nf
        field_simp
        linarith
      -- Case analysis on whether p = 1
      by_cases g2 : p = 1
      .
        -- If p = 1, then all variables equal 1
        rw [g2] at h1 h2 h3 h4
        simp at h1 h2 h3 h4
        replace h1 : x1 = 1:= by linarith
        replace h2 : x2 = 1:= by linarith
        replace h3 : x3 = 1:= by linarith
        replace h4 : x4 = 1:= by linarith
        subst x1 x2 x3 x4
        simp
      .
        -- If p ≠ 1, then 1 - p > 0
        replace g1 : 1 - p > 0:= by
          by_contra H
          simp at H
          replace H : p = 1:= by linarith
          trivial
        clear g2
        simp at h1 h2 h3 h4
        -- Each variable is either 1 + √(1-p) or 1 - √(1-p)
        replace h1 : x1 = 1 + √(1 - p) ∨ x1 = 1 - √(1 - p):= by
          rcases h1 with h1 | h1
          .
            left
            linarith
          .
            right
            linarith
        replace h2 : x2 = 1 + √(1 - p) ∨ x2 = 1 - √(1 - p):= by
          rcases h2 with h2 | h2
          .
            left
            linarith
          .
            right
            linarith
        replace h3 : x3 = 1 + √(1 - p) ∨ x3 = 1 - √(1 - p):= by
          rcases h3 with h3 | h3
          .
            left
            linarith
          .
            right
            linarith
        replace h4 : x4 = 1 + √(1 - p) ∨ x4 = 1 - √(1 - p):= by
          rcases h4 with h4 | h4
          .
            left
            linarith
          .
            right
            linarith
        -- Define s = 1 - p for convenience
        set s:= 1 - p with hs
        clear_value s
        -- Prove impossibility of having 3 variables equal to 1 + √s and 1 equal to 1 - √s
        have g2 : p = (1 + √s) ^ 3 * (1 - √s) → False:= by
          intro g2
          rw [show (1 + √s) ^ 3 * (1 - √s) = (1 + √s) ^ 2 * ((1 + √s) * (1 - √s)) by ring] at g2
          rw [show (1 + √s) * (1 - √s) = p by ring_nf ; field_simp ; subst s ; linarith] at g2
          replace g2 : p * √s * (2 + √s) = 0:= by linarith
          simp [h5] at g2
          rcases g2 with g2 | g2
          all_goals
            replace g1 : √s > 0:= by positivity
            linarith
        -- Prove impossibility of having 2 variables each equal to 1 + √s and 1 - √s
        have g3 : p = (1 + √s) ^ 2 * (1 - √s) ^ 2 → False:= by
          intro g3
          rw [show (1 + √s) ^ 2 * (1 - √s) ^ 2 = ((1 + √s) * (1 - √s)) ^ 2 by ring] at g3
          rw [show (1 + √s) * (1 - √s) = p by ring_nf ; field_simp ; subst s ; linarith] at g3
          replace g3 : p * (p - 1) = 0:= by linarith
          simp [h5] at g3
          linarith
        -- Prove that if 1 variable equals 1 + √s and 3 equal 1 - √s, then √s = 2
        have g4 : p = (1 + √s) * (1 - √s) ^ 3 → √s = 2:= by
          intro g4
          rw [show (1 + √s) * (1 - √s) ^ 3 = (1 + √s) * (1 - √s) * (1 - √s) ^ 2 by ring] at g4
          rw [show (1 + √s) * (1 - √s) = p by ring_nf ; field_simp ; subst s ; linarith] at g4
          replace g4 : p * √s * (2 - √s) = 0:= by linarith
          simp [h5] at g4
          rcases g4 with g4 | g4
          .
            replace g1 : √s > 0:= by positivity
            linarith
          .
            replace g4 : √s = 2:= by linarith
            replace g4 : √s ^ 2 = 4:= by rw [g4] ; ring_nf
            field_simp at g4
            rw [g4]
            rw [show (4 : ℝ) = 2 ^ 2 by ring_nf]
            field_simp
        -- Exhaustive case analysis on all 16 combinations of variable values
        rcases h1 with h1 | h1
        all_goals
          rcases h2 with h2 | h2
          all_goals
            rcases h3 with h3 | h3
            all_goals
              rcases h4 with h4 | h4
              all_goals
                subst x1 x2 x3 x4
                simp at h
        .
          -- Case: all variables = 1 + √s (impossible by g2)
          replace g2:= g2 (by linarith only [hp])
          simp at g2
        .
          -- Case: 3 variables = 1 + √s, 1 = 1 - √s (impossible by g2)
          replace g2:= g2 (by linarith only [hp])
          simp at g2
        .
          -- Case: 2 variables = 1 + √s, 2 = 1 - √s (impossible by g3)
          replace g3:= g3 (by linarith only [hp])
          simp at g3
        .
          -- Case: 3 variables = 1 + √s, 1 = 1 - √s (impossible by g2)
          replace g2:= g2 (by linarith only [hp])
          simp at g2
        .
          -- Case: 2 variables = 1 + √s, 2 = 1 - √s (impossible by g3)
          replace g3:= g3 (by linarith only [hp])
          simp at g3
        .
          -- Case: 2 variables = 1 + √s, 2 = 1 - √s (impossible by g3)
          replace g3:= g3 (by linarith only [hp])
          simp at g3
        .
          -- Case: 1 variable = 1 + √s, 3 = 1 - √s (gives solution with √s = 2)
          replace g4:= g4 (by linarith only [hp])
          rw [g4]
          norm_num
        .
          -- Case: 3 variables = 1 + √s, 1 = 1 - √s (impossible by g2)
          replace g2:= g2 (by linarith only [hp])
          simp at g2
        .
          -- Case: 2 variables = 1 + √s, 2 = 1 - √s (impossible by g3)
          replace g3:= g3 (by linarith only [hp])
          simp at g3
        .
          -- Case: 2 variables = 1 + √s, 2 = 1 - √s (impossible by g3)
          replace g3:= g3 (by linarith only [hp])
          simp at g3
        .
          -- Case: 1 variable = 1 + √s, 3 = 1 - √s (gives solution with √s = 2)
          replace g4:= g4 (by linarith only [hp])
          rw [g4]
          norm_num
        .
          -- Case: 2 variables = 1 + √s, 2 = 1 - √s (impossible by g3)
          replace g3:= g3 (by linarith only [hp])
          simp at g3
        .
          -- Case: 1 variable = 1 + √s, 3 = 1 - √s (gives solution with √s = 2)
          replace g4:= g4 (by linarith only [hp])
          rw [g4]
          norm_num
        .
          -- Case: 1 variable = 1 + √s, 3 = 1 - √s (gives solution with √s = 2)
          replace g4:= g4 (by linarith only [hp])
          rw [g4]
          norm_num
  .
    -- Backward direction: if (x1,x2,x3,x4) is one of the 5 solutions, then it satisfies the system
    intro h
    simp at h
    -- Check each of the 5 candidate solutions
    rcases h with h | h | h | h | h
    all_goals
      rcases h with ⟨h1, h2, h3, h4⟩
      subst x1 x2 x3 x4
      -- Verify by direct computation that each solution satisfies all 4 equations
      norm_num
