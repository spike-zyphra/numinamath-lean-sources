import Mathlib
/- Determine all pairs $(a, b)$ of real numbers such that $10, a, b, a b$ is an arithmetic progression. -/
theorem algebra_608304 : {(a, b) : ℝ × ℝ | a - 10 = b - a ∧ b - a = a * b - b} = {(4, -2), (5 / 2, -5)}:= by
  -- Use extensionality to prove equality of sets
  ext ⟨a, b⟩
  constructor
  -- Forward direction: if (a,b) satisfies the conditions, it must be one of the two pairs
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    -- From first condition: a = (b + 10)/2
    replace h1 : a = (b + 10) / 2:= by linarith
    subst a
    -- Simplify to get quadratic equation: (b + 2)(b + 5) = 0
    replace h2 : (b + 2) * (b + 5) = 0:= by linarith
    simp at h2
    rcases h2 with h2 | h2
    -- First solution: b = -2 leads to a = 4
    .
      replace h2 : b = -2:= by linarith
      subst b
      simp
      norm_num
    -- Second solution: b = -5 leads to a = 5/2
    .
      replace h2 : b = -5:= by linarith
      subst b
      simp
      norm_num
  -- Reverse direction: verify that both pairs satisfy the conditions
  .
    intro h
    simp at h
    rcases h with h | h
    all_goals
      rcases h with ⟨h1, h2⟩
      subst a b
      simp
      norm_num
