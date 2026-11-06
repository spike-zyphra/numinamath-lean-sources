import Mathlib
/- Example 7 Let $\alpha$ be an integer. If there exist integers $b$ and $c$ such that $(x+\alpha)(x-15)-25=(x+b)(x+c)$ holds, find the possible values of $\alpha$. -/
theorem algebra_306980 : {a : ℤ | ∃ b c : ℤ, ∀ x : ℝ, (x + a) * (x - 15) - 25 = (x + b) * (x + c)} = {9, -15, -39}:= by
  -- Use extensionality to prove set equality
  ext a
  simp
  constructor
  -- Forward direction: if the equation holds, then a ∈ {9, -15, -39}
  .
    intro h
    -- Extract the witnesses b and c
    rcases h with ⟨b, c, h⟩
    -- Evaluate the equation at x = 0
    have h1:= h 0
    -- Evaluate the equation at x = 15
    have h2:= h 15
    simp at h1 h2
    -- From x = 15: (15 + b)(15 + c) = -25
    replace h2 : (15 + b) * (15 + c) = -25:= by
      rify
      linarith
    -- From x = 0: 15a = -bc - 25
    replace h1 : 15 * a = -b * c - 25:= by
      rify
      linarith
    -- Since (15+b)(15+c) = -25, we have |15+b| * |15+c| = 25
    replace h : (15 + b).natAbs * (15 + c).natAbs = 25:= by
      zify
      rw [show |15 + b| * |15 + c| = |(15 + b) * (15 + c)| by exact Eq.symm (abs_mul (15 + b) (15 + c))]
      rw [h2]
      norm_num
    -- Therefore |15+b| divides 25
    replace h : (15 + b).natAbs ∈ Nat.divisors 25:= by
      suffices (15 + b).natAbs ∣ 25 by refine Nat.mem_divisors.mpr ⟨this, by norm_num⟩
      rw [←h]
      simp
    -- The divisors of 25 are {1, 5, 25}
    have h3 : Nat.divisors 25 = {1, 5, 25}:= by native_decide
    rw [h3] at h
    simp at h
    -- Case analysis on the possible values of |15+b|
    rcases h with h | h | h
    all_goals
      zify at h
    -- Case 1: |15+b| = 1
    .
      -- Either 15+b = 1 or 15+b = -1
      replace h : 15 + b = 1 ∨ 15 + b = -1:= by exact abs_eq_abs.mp h
      rcases h with h | h
      -- Subcase 1a: 15+b = 1, so b = -14
      .
        rw [h] at h2
        replace h : b = -14:= by linarith
        -- From (15+b)(15+c) = -25: 1*(15+c) = -25, so c = -40
        replace h2 : c = -40:= by linarith
        subst b c
        -- From 15a = -bc - 25: a = -39
        replace h1 : a = -39:= by linarith
        subst a
        simp
      -- Subcase 1b: 15+b = -1, so b = -16
      .
        rw [h] at h2
        replace h : b = -16:= by linarith
        -- From (15+b)(15+c) = -25: (-1)*(15+c) = -25, so c = 10
        replace h2 : c = 10:= by linarith
        subst b c
        -- From 15a = -bc - 25: a = 9
        replace h1 : a = 9:= by linarith
        subst a
        simp
    -- Case 2: |15+b| = 5
    .
      -- Either 15+b = 5 or 15+b = -5
      replace h : 15 + b = 5 ∨ 15 + b = -5:= by exact abs_eq_abs.mp h
      rcases h with h | h
      -- Subcase 2a: 15+b = 5, so b = -10
      .
        rw [h] at h2
        replace h : b = -10:= by linarith
        -- From (15+b)(15+c) = -25: 5*(15+c) = -25, so c = -20
        replace h2 : c = -20:= by linarith
        subst b c
        -- From 15a = -bc - 25: a = -15
        replace h1 : a = -15:= by linarith
        subst a
        simp
      -- Subcase 2b: 15+b = -5, so b = -20
      .
        rw [h] at h2
        replace h : b = -20:= by linarith
        -- From (15+b)(15+c) = -25: (-5)*(15+c) = -25, so c = -10
        replace h2 : c = -10:= by linarith
        subst b c
        -- From 15a = -bc - 25: a = -15
        replace h1 : a = -15:= by linarith
        subst a
        simp
    -- Case 3: |15+b| = 25
    .
      -- Either 15+b = 25 or 15+b = -25
      replace h : 15 + b = 25 ∨ 15 + b = -25:= by exact abs_eq_abs.mp h
      rcases h with h | h
      -- Subcase 3a: 15+b = 25, so b = 10
      .
        rw [h] at h2
        replace h : b = 10:= by linarith
        -- From (15+b)(15+c) = -25: 25*(15+c) = -25, so c = -16
        replace h2 : c = -16:= by linarith
        subst b c
        -- From 15a = -bc - 25: a = 9
        replace h1 : a = 9:= by linarith
        subst a
        simp
      -- Subcase 3b: 15+b = -25, so b = -40
      .
        rw [h] at h2
        replace h : b = -40:= by linarith
        -- From (15+b)(15+c) = -25: (-25)*(15+c) = -25, so c = -14
        replace h2 : c = -14:= by linarith
        subst b c
        -- From 15a = -bc - 25: a = -39
        replace h1 : a = -39:= by linarith
        subst a
        simp
  -- Backward direction: if a ∈ {9, -15, -39}, then the equation holds
  .
    intro h
    simp at h
    -- Case analysis on the three possible values of a
    rcases h with h | h | h
    all_goals
      subst a
      simp
    -- Case a = 9: use b = -16, c = 10
    .
      use -16, 10
      intro x
      simp
      linarith
    -- Case a = -15: use b = -10, c = -20
    .
      use -10, -20
      intro x
      simp
      linarith
    -- Case a = -39: use b = -40, c = -14
    .
      use -40, -14
      intro x
      simp
      linarith
