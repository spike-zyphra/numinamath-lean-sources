import Mathlib
/- Real numbers $x,y,a$ satisfy the equations $x+y = x^3 +y^3 = x^5 +y^5 = a$.
Find all possible values of $a$. -/
theorem algebra_87556 : {a : ℝ | ∃ x y : ℝ, x + y = a ∧ x ^ 3 + y ^ 3 = a ∧ x ^ 5 + y ^ 5 = a} = {0, 1, -1, 2, -2}:= by
  ext a
  constructor
  -- Forward direction: if a is in the set, then a must be one of {0, 1, -1, 2, -2}
  .
    intro h
    rcases h with ⟨x, y, h1, h2, h3⟩
    -- Derive that (x + y) * (x^2 - x*y + y^2 - 1) = 0 from the given equations
    have h4 : (x + y) * (x ^ 2 - x * y + y ^ 2 - 1) = 0:= by linarith
    simp at h4
    rcases h4 with h4 | h4
    -- Case 1: x + y = 0, which means a = 0
    .
      rw [h1] at h4
      subst a
      rw [h4]
      simp
    -- Case 2: x^2 - x*y + y^2 = 1
    .
      -- Manipulate the equations to derive constraints on a
      replace h2 : (x ^ 2 + y ^ 2) * (x ^ 3 + y ^ 3) = (x ^ 2 + y ^ 2) * a:= by rw [h2]
      replace h3 : (x * y) ^ 2 * (x + y) = ((x + y) ^ 2 - x * y * 2 - 1) * a:= by linarith
      replace h4 : x * y = 1 / 3 * ((x + y) ^ 2 - 1):= by linarith
      rw [h1] at h3 h4
      rw [h4] at h3
      -- Derive that a(a-1)(a+1)(a-2)(a+2) = 0, which means a ∈ {0, 1, -1, 2, -2}
      replace h3 : a * (a - 1) * (a + 1) * (a - 2) * (a + 2) = 0:= by linarith
      simp at h3
      clear h1
      rcases h3 with h3 | h3
      -- Handle each possible value of a
      .
        rcases h3 with h3 | h3
        .
          rcases h3 with h3 | h3
          .
            rcases h3 with h3 | h3
            -- Case a = 0
            .
              subst a
              simp
            -- Case a = 1
            .
              replace h3 : a = 1:= by linarith
              subst a
              simp
          -- Case a = -1
          .
            replace h3 : a = -1:= by linarith
            subst a
            simp
        -- Case a = 2
        .
          replace h3 : a = 2:= by linarith
          subst a
          simp
      -- Case a = -2
      .
        replace h3 : a = -2:= by linarith
        subst a
        simp
  -- Backward direction: if a is one of {0, 1, -1, 2, -2}, then there exist x and y satisfying the system
  .
    intro h
    simp at h
    rcases h with h | h | h | h | h
    all_goals
      subst a
      simp
    -- For a = 0, use x = 0, y = 0
    .
      use 0, 0
      simp
    -- For a = 1, use x = 1, y = 0
    .
      use 1, 0
      simp
    -- For a = -1, use x = -1, y = 0
    .
      use -1, 0
      simp
      norm_num
    -- For a = 2, use x = 1, y = 1
    .
      use 1, 1
      simp
      norm_num
    -- For a = -2, use x = -1, y = -1
    .
      use -1, -1
      norm_num
