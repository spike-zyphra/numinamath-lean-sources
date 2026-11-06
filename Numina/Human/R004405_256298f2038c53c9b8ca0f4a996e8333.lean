import Mathlib
/- 4. Find all quadratic trinomials $P(x)=a x^{2}+b x+c$ with integer coefficients $a, b$, and $c$, for which $P(1)< P(2)< P(3)$ and $(P(1))^{2}+(P(2))^{2}+(P(3))^{2}=22$. -/
theorem algebra_261609 : {P : ℤ → ℤ | (∃ a b c : ℤ, P = fun x => a * x ^ 2 + b * x + c) ∧ P 1 < P 2 ∧ P 2 < P 3 ∧ P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 = 22} = {fun x => 2 * x ^ 2 - 5 * x, fun x => -2 * x ^ 2 + 11 * x - 12}:= by
  ext P
  constructor
  -- Forward direction: if P satisfies the conditions, then P is one of the two specific polynomials
  .
    intro h
    simp at h
    rcases h with ⟨⟨a, b, c, hP⟩, ⟨h1, h2, h3⟩⟩
    -- Key lemma: for non-negative integers x, y, z with x² + y² + z² = 22,
    -- the only possibilities are permutations of (2, 3, 3)
    have h4 : ∀ x y z : ℤ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x ^ 2 + y ^ 2 + z ^ 2 = 22 → (x = 2 ∧ y = 3 ∧ z = 3) ∨ (x = 3 ∧ y = 2 ∧ z = 3) ∨ (x = 3 ∧ y = 3 ∧ z = 2):= by
      intro x y z hx hy hz h4
      -- Sub-lemma: if x ≤ y ≤ z and x² + y² + z² = 22, then (x, y, z) = (2, 3, 3)
      have h5 : ∀ x y z : ℤ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x ≤ y → y ≤ z → x ^ 2 + y ^ 2 + z ^ 2 = 22 → (x = 2 ∧ y = 3 ∧ z = 3):= by
        intro x y z hx hy hz hxy hyz h4
        -- Upper bound: z ≤ 4 (since z² ≤ 22 implies z ≤ 4 for positive z)
        have g1 : z ≤ 4:= by
          by_contra H
          simp at H
          replace H : z ≥ 5:= by omega
          replace H : z ^ 2 ≥ 25:= by nlinarith only [H]
          have g2 : x ^ 2 + y ^ 2 ≥ 0:= by positivity
          linarith
        -- Lower bound: z ≥ 3 (since if z ≤ 2, then x² + y² + z² ≤ 12 < 22)
        have g2 : z ≥ 3:= by
          by_contra H
          simp at H
          replace H : z ≤ 2:= by omega
          replace hxy : x ≤ 2:= by omega
          replace hyz : y ≤ 2:= by omega
          replace H : z ^ 2 ≤ 4:= by nlinarith only [H, hz]
          replace hxy : x ^ 2 ≤ 4:= by nlinarith only [hxy, hx]
          replace hyz : y ^ 2 ≤ 4:= by nlinarith only [hyz, hy]
          linarith
        -- Therefore z = 3 or z = 4
        replace g1 : z = 3 ∨ z = 4:= by omega
        rcases g1 with g1 | g1
        -- Case 1: z = 3
        .
          subst z
          -- If z = 3, then y = 3 (similar argument as for z)
          replace g2 : y = 3:= by
            by_contra H
            replace H : y ≤ 2:= by omega
            replace hxy : x ≤ 2:= by omega
            replace H : y ^ 2 ≤ 4:= by nlinarith only [H, hy]
            replace hxy : x ^ 2 ≤ 4:= by nlinarith only [hxy, hx]
            linarith
          subst y
          -- If y = z = 3, then x² + 9 + 9 = 22, so x² = 4, hence x = 2
          replace h4 : (x - 2) * (x + 2) = 0:= by linarith
          simp [show x + 2 ≠ 0 by omega] at h4
          replace h4 : x = 2:= by omega
          subst x
          simp
        -- Case 2: z = 4
        .
          subst z
          -- If z = 4, then y ≤ 2 (since y ≥ 3 would make the sum too large)
          replace g2 : y ≤ 2:= by
            by_contra H
            simp at H
            replace H : y ≥ 3:= by omega
            replace H : y ^ 2 ≥ 9:= by nlinarith only [H]
            have g3 : x ^ 2 ≥ 0:= by positivity
            linarith
          -- If z = 4 and y ≤ 2, then y = 2 (similar argument)
          replace g2 : y = 2:= by
            by_contra H
            replace H : y ≤ 1:= by omega
            replace hxy : x ≤ 1:= by omega
            replace H : y ^ 2 ≤ 1:= by nlinarith only [H, hy]
            replace hxy : x ^ 2 ≤ 1:= by nlinarith only [hxy, hx]
            linarith
          subst y
          -- If y = 2 and z = 4, then x² + 4 + 16 = 22, so x² = 2
          -- But 2 is not a perfect square, contradiction
          replace h4 : x ^ 2 = 2:= by omega
          replace h4 : IsSquare (2 : ℤ):= by
            use x
            linarith
          absurd h4
          native_decide
      -- Consider all possible orderings of x, y, z
      have h6 : x ≤ y ∧ y ≤ z ∨ x ≤ z ∧ z ≤ y ∨ y ≤ x ∧ x ≤ z ∨ y ≤ z ∧ z ≤ x ∨ z ≤ x ∧ x ≤ y ∨ z ≤ y ∧ y ≤ x:= by omega
      rcases h6 with h6 | h6 | h6 | h6 | h6 | h6
      all_goals
        rcases h6 with ⟨h6, h7⟩
      -- Apply the sub-lemma to each ordering
      .
        replace h5:= h5 x y z hx hy hz h6 h7 h4
        rcases h5 with ⟨gx, gy, gz⟩
        subst x y z
        simp
      .
        replace h5:= h5 x z y hx hz hy h6 h7 (by linarith)
        rcases h5 with ⟨gx, gy, gz⟩
        subst x y z
        simp
      .
        replace h5:= h5 y x z hy hx hz h6 h7 (by linarith)
        rcases h5 with ⟨gx, gy, gz⟩
        subst x y z
        simp
      .
        replace h5:= h5 y z x hy hz hx h6 h7 (by linarith)
        rcases h5 with ⟨gx, gy, gz⟩
        subst x y z
        simp
      .
        replace h5:= h5 z x y hz hx hy h6 h7 (by linarith)
        rcases h5 with ⟨gx, gy, gz⟩
        subst x y z
        simp
      .
        replace h5:= h5 z y x hz hy hx h6 h7 (by linarith)
        rcases h5 with ⟨gx, gy, gz⟩
        subst x y z
        simp
    -- Convert squares to absolute values
    rw [show P 1 ^ 2 = |P 1| ^ 2 by exact Eq.symm (sq_abs (P 1))] at h3
    rw [show P 2 ^ 2 = |P 2| ^ 2 by exact Eq.symm (sq_abs (P 2))] at h3
    rw [show P 3 ^ 2 = |P 3| ^ 2 by exact Eq.symm (sq_abs (P 3))] at h3
    -- Apply the key lemma to |P(1)|, |P(2)|, |P(3)|
    specialize h4 |P 1| |P 2| |P 3| (by positivity) (by positivity) (by positivity) h3
    rcases h4 with h4 | h4 | h4
    all_goals
      rcases h4 with ⟨hx, hy, hz⟩
    -- Case 1: |P(1)| = 2, |P(2)| = 3, |P(3)| = 3
    .
      replace hx : P 1 = 2 ∨ P 1 = -2:= by exact abs_eq_abs.mp hx
      replace hy : P 2 = 3 ∨ P 2 = -3:= by exact abs_eq_abs.mp hy
      replace hz : P 3 = 3 ∨ P 3 = -3:= by exact abs_eq_abs.mp hz
      -- This case is impossible given P(1) < P(2) < P(3)
      omega
    -- Case 2: |P(1)| = 3, |P(2)| = 2, |P(3)| = 3
    .
      replace hx : P 1 = 3 ∨ P 1 = -3:= by exact abs_eq_abs.mp hx
      replace hy : P 2 = 2 ∨ P 2 = -2:= by exact abs_eq_abs.mp hy
      replace hz : P 3 = 3 ∨ P 3 = -3:= by exact abs_eq_abs.mp hz
      -- Given the ordering constraint, only two subcases are possible
      have h4 : P 1 = -3 ∧ P 2 = -2 ∧ P 3 = 3 ∨ P 1 = -3 ∧ P 2 = 2 ∧ P 3 = 3:= by omega
      clear hx hy hz
      rcases h4 with h4 | h4
      all_goals
        rcases h4 with ⟨hx, hy, hz⟩
        simp [hP] at hx hy hz
      -- Subcase 2a: P(1) = -3, P(2) = -2, P(3) = 3
      .
        -- Solve the system of equations to find a, b, c
        replace hx : a = 2:= by linarith
        replace hy : b = -5:= by linarith
        replace hz : c = 0:= by linarith
        subst a b c P
        simp
        left
        funext x
        ring_nf
      -- Subcase 2b: P(1) = -3, P(2) = 2, P(3) = 3
      .
        -- Solve the system of equations to find a, b, c
        replace hx : a = -2:= by linarith
        replace hy : b = 11:= by linarith
        replace hz : c = -12:= by linarith
        subst a b c P
        simp
        right
        funext x
        ring_nf
    -- Case 3: |P(1)| = 3, |P(2)| = 3, |P(3)| = 2
    .
      replace hx : P 1 = -3 ∨ P 1 = 3:= by exact abs_eq_abs.mp hx
      replace hy : P 2 = -3 ∨ P 2 = 3:= by exact abs_eq_abs.mp hy
      replace hz : P 3 = -2 ∨ P 3 = 2:= by exact abs_eq_abs.mp hz
      -- This case is impossible given P(1) < P(2) < P(3)
      omega
  -- Backward direction: verify that the two specific polynomials satisfy the conditions
  .
    intro h
    simp at h
    rcases h with h | h
    all_goals
      subst P
      simp
    -- Verify P(x) = 2x² - 5x satisfies all conditions
    .
      use 2, -5, 0
      simp
      funext x
      ring_nf
    -- Verify P(x) = -2x² + 11x - 12 satisfies all conditions
    .
      use -2, 11, -12
      simp
      funext x
      ring_nf
