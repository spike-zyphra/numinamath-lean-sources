import Mathlib

theorem algebra_2667 :
    ∀ m ∈ Set.Icc 5 15, ∀ n ∈ Set.Icc 20 30, m / n ∈ Set.Icc (1 / 6) (7 / 8) := by
  intro m hm n hn
  rcases hm with ⟨h1, h2⟩
  rcases hn with ⟨h3, h4⟩
  -- Let's think about the decimals. 
  -- We need to show 1/6 ≤ m/n ≤ 7/8.
  -- When m=5, n=30: 5/30=1/6≈0.1667.
  -- When m=15, n=20: 15/20=3/4=0.75.
  -- When m=5, n=20: 5/20=1/4=0.25.
  -- When m=5, n=20: 5/20=1/4=0.25.
  -- When m=15, n=30: 15/30=0.5.
  have h5 : (n : ℝ) ≥ (20 : ℝ) := by exact_mod_cast h3
  have h6 : (n : ℝ) ≤ (30 : ℝ) := by exact_mod_cast h4
  have h7 : (m : ℝ) ≥ (5 : ℝ) := by exact_mod_cast h1
  have h8 : (m : ℝ) ≤ (15 : ℝ) := by exact_mod_cast h2
  
  -- First part: Show 1/6 ≤ m/n 
  -- Convert to showing 1/6 * n ≤ m
  have eq1 : (1 : ℝ) / 6 * (n : ℝ) ≤ (m : ℝ) := by
    have hn30 : (n : ℝ) ≤ (30 : ℝ) := by exact_mod_cast h4
    have hm5 : (m : ℝ) ≥ (5 : ℝ) := by exact_mod_cast h1
    nlinarith
  
  -- Second part: Show m/n ≤ 7/8
  -- Convert to showing m ≤ 7/8 * n
  have eq2 : (m : ℝ) ≤ (7 : ℝ) / 8 * (n : ℝ) := by
    have hn20 : (n : ℝ) ≥ (20 : ℝ) := by exact_mod_cast h3
    have hm15 : (m : ℝ) ≤ (15 : ℝ) := by exact_mod_cast h2
    nlinarith
  
  -- Now connect that to set membership.
  -- First, we have to show 1/6 ≤ m/n
  -- Then, we have to show m/n ≤ 7/8

  simp [Set.mem_Icc]
  -- The simpler is generating 5 conditions, and we need to carefully handle them
  -- The main idea is that divisibility in Nat increases with numerator and decreases with denominator
  -- So the minimum is at min m / max n, and maximum is at max m / min n.
  -- min m = 5, max n = 30. So the minimum value is 5 / 30 = 1 / 6
  -- max m = 15, min n = 20. So the maximum value is 15 / 20 = 3 / 4

  -- Using `interval_cases` to try out all cases
  -- But the interval_cases will generate too many cases for m and n.

  -- Use Lean's Rational Inequality
  all_goals
    try { omega }
    try { 
      apply (le_div_iff₀' (by omega)).mpr
      nlinarith
    }
    try 
      { 
        apply (div_le_iff₀ (by omega)).mpr
        nlinarith
      }