import Mathlib

open Real

/- 1. If $\frac{100}{x}>\sqrt{1994}-25>\frac{125}{x+2}$, then the positive integer $x$ is ( ).
(A) 4
(B) 5
(C) 6
(D) 7 -/
theorem inequalities_300987 {x : ℤ} (hx : x > 0) (h : 100 / x > sqrt 1994 - 25 ∧ sqrt 1994 - 25 > 125 / (x + 2)) :
    x = 5 := by
  -- Split the conjunction into two separate hypotheses
  rcases h with ⟨h1, h2⟩

  -- Establish bounds for sqrt(1994) using numerical approximations
  -- Lower bound: sqrt(1994) > 44.6
  have h3 : 44.6 < sqrt 1994 := by
    rw [Real.lt_sqrt] <;> norm_num

  -- Upper bound: sqrt(1994) < 44.7
  have h4 : sqrt 1994 < 44.7 := by
    rw [Real.sqrt_lt] <;> norm_num

  -- Prove that x ≤ 5 by contradiction
  have h5 : x ≤ 5 := by
    by_contra hx'
    push_neg at hx'

    -- If x > 5, then x ≥ 6 (since x is an integer)
    have h5 : x ≥ 6 := by linarith

    -- If x ≥ 6, then 100/x ≤ 100/6
    have h6 : (100 : ℝ) / x ≤ (100 : ℝ) / 6 := by
      have h7 : (x : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h5
      apply (div_le_div_iff (by linarith) (by linarith)).mpr
      all_goals linarith

    -- Use the lower bound of sqrt(1994) > 44.6
    have h7 : (sqrt 1994 : ℝ) > (44.6 : ℝ) := by
      exact_mod_cast h3

    -- Therefore sqrt(1994) - 25 > 19.6
    have h8 : (sqrt 1994 : ℝ) - (25 : ℝ) > (19.6 : ℝ) := by
      norm_num
      norm_num at h7
      linarith [h7]

    -- From the first inequality, 100/x > sqrt(1994) - 25 > 19.6
    have h9 : (100 : ℝ) / x > (19.6 : ℝ) := by
      have h10 : (100 : ℝ) / x > (sqrt 1994 : ℝ) - (25 : ℝ) := by
        exact_mod_cast h1
      linarith [h10, h8]

    -- But 100/6 < 19.6, which is a numerical fact
    have h10 : (100 : ℝ) / (6 : ℝ) < (19.6 : ℝ) := by norm_num

    -- We have 100/x ≤ 100/6 < 19.6 < 100/x, which is a contradiction
    have h11 : (100 : ℝ) / x ≤ (100 : ℝ) / (6 : ℝ) := by linarith [h6]
    linarith [h9, h10, h11]

  -- Prove that x ≥ 5 by contradiction
  have h10 : x ≥ 5 := by
    by_contra hx'
    push_neg at hx'

    -- If x < 5, then x ≤ 4 (since x is an integer)
    have h11 : x ≤ 4 := by linarith

    -- If x ≤ 4, then x + 2 ≤ 6
    have h12 : (x : ℝ) + (2 : ℝ) ≤ (6 : ℝ) := by
      have h13 : (x : ℝ) ≤ (4 : ℝ) := by exact_mod_cast h11
      linarith

    -- If x + 2 ≤ 6, then 125/(x+2) ≥ 125/6
    have h13 : (125 : ℝ) / (x + 2) ≥ (125 : ℝ) / (6 : ℝ) := by
      have h14 : (x : ℝ) + (2 : ℝ) > 0 := by
        have h15 : (x : ℝ) > 0 := by exact_mod_cast hx
        linarith
      have h17 : (x : ℝ) + (2 : ℝ) ≤ (6 : ℝ) := by linarith [h12]
      apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      nlinarith [h17]

    -- From the second inequality, sqrt(1994) - 25 > 125/(x+2) ≥ 125/6
    have h14 : (sqrt 1994 : ℝ) - (25 : ℝ) > (125 : ℝ) / (6 : ℝ) := by
      linarith

    -- Use the upper bound of sqrt(1994) < 44.7
    have h15 : (sqrt 1994 : ℝ) < (44.7 : ℝ) := by
      exact_mod_cast h4

    -- Therefore sqrt(1994) - 25 < 19.7
    have h16 : (sqrt 1994 : ℝ) - (25 : ℝ) < (19.7 : ℝ) := by
      norm_num
      norm_num at h15
      linarith [h15]

    -- But 125/6 > 19.7, which is a numerical fact
    have h17 : (125 : ℝ) / (6 : ℝ) > (19.7 : ℝ) := by norm_num

    -- We have sqrt(1994) - 25 > 125/6 > 19.7 > sqrt(1994) - 25, which is a contradiction
    linarith [h14, h16, h17]

  -- Since x ≤ 5 and x ≥ 5, we conclude that x = 5
  have h11 : x = 5 := by
    linarith
  exact h11
