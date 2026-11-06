import Mathlib
/- Find all real solutions $(x, y)$ of the system $x^{2}+y=12=y^{2}+x$. -/
theorem algebra_611425 : {(x, y) : ℝ × ℝ | x ^ 2 + y = 12 ∧ y ^ 2 + x = 12} = {(3, 3), (-4, -4), ((1 + 3 * √5) / 2, (1 - 3 * √5) / 2), ((1 - 3 * √5) / 2, (1 + 3 * √5) / 2)}:= by
  ext ⟨x, y⟩
  constructor
  -- Forward direction: prove that any solution must be one of these four points
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    -- Key step: show that (x - y)(x + y - 1) = 0
    have h3 : (x - y) * (x + y - 1) = 0:= by linarith
    simp at h3
    rcases h3 with h3 | h3
    -- Case 1: x = y
    .
      replace h3 : x = y:= by linarith
      subst x
      -- When x = y, we get (y - 3)(y + 4) = 0
      replace h1 : (y - 3) * (y + 4) = 0:= by linarith
      simp at h1
      rcases h1 with h1 | h1
      -- Subcase 1.1: y = 3 (gives point (3,3))
      .
        replace h1 : y = 3:= by linarith
        subst y
        simp
      -- Subcase 1.2: y = -4 (gives point (-4,-4))
      .
        replace h1 : y = -4:= by linarith
        subst y
        simp
    -- Case 2: x + y = 1
    .
      replace h3 : x = 1 - y:= by linarith
      subst x
      -- This leads to a quadratic in y with solutions involving √5
      replace h1 : (y - (1 - 3 * √5) / 2) * (y - (1 + 3 * √5) / 2) = 0:= by
        ring_nf
        field_simp
        linarith
      simp at h1
      rcases h1 with h1 | h1
      -- Subcase 2.1: First solution with √5
      .
        replace h1 : y = (1 - 3 * √5) / 2:= by linarith
        subst y
        simp
        right
        right
        left
        ring_nf
      -- Subcase 2.2: Second solution with √5
      .
        replace h1 : y = (1 + 3 * √5) / 2:= by linarith
        subst y
        simp
        right
        right
        right
        ring_nf
  -- Backward direction: verify that each of the four points satisfies the equations
  .
    intro h
    simp at h
    rcases h with h | h | h | h
    all_goals
      rcases h with ⟨h1, h2⟩
      subst x y
      simp
      ring_nf
    all_goals
      field_simp
      ring_nf
