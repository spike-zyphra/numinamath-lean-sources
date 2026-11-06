import Mathlib
/- For how many positive integers $a$ does the polynomial

$$
x^{2}-a x+a
$$

have an integer root? -/
theorem algebra_610060 : {a : ℤ | a > 0 ∧ ∃ x : ℤ, x ^ 2 - a * x + a = 0}.ncard = 1:= by
  -- Prove that the set of valid 'a' contains only {4}
  have h : {a : ℤ | a > 0 ∧ ∃ x : ℤ, x ^ 2 - a * x + a = 0} = {4}:= by
    ext a
    constructor
    -- Forward direction: if 'a' is in the set, then a = 4
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      rcases h2 with ⟨x, h2⟩
      simp
      -- Rewrite the equation to show (x-1)(a-x-1) = 1
      replace h2 : (x - 1) * (a - x - 1) = 1:= by linarith
      -- Since product is 1, x-1 must be either 1 or -1
      have h3 : x - 1 = 1 ∨ x - 1 = -1:= by exact Int.eq_one_or_neg_one_of_mul_eq_one h2
      rcases h3 with h3 | h3
      -- Case 1: x-1 = 1, which means x = 2
      .
        rw [h3] at h2
        replace h3 : x = 2:= by linarith
        linarith
      -- Case 2: x-1 = -1, which means x = 0
      .
        rw [h3] at h2
        replace h3 : x = 0:= by linarith
        subst x
        simp at h2
        by_contra _
        linarith
    -- Backward direction: prove that 4 is in the set
    .
      intro h
      simp at h
      subst a
      simp
      -- Show that x = 2 is a solution when a = 4
      use 2
      simp
  rw [h]
  simp
