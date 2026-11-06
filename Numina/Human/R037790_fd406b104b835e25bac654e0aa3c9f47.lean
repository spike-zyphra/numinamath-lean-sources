import Mathlib
/- 5. The equation $x^{2}+b x+c=0$ has two different integer solutions, and the equation $x^{2}+b x-c=0$ also has two different integer solutions, where $b$ and $c$ are nonzero.
(i) Show that it is possible to find different positive integers $p$ and $q$ such that $2 b^{2}=p^{2}+q^{2}$.
(ii) Show that it is possible to find different positive integers $r$ and $s$ such that $b^{2}=r^{2}+s^{2}$. -/
theorem algebra_237937 {b c : ℤ} (hb : b ≠ 0) (hc : c ≠ 0) (h1 : ∃ x y, x ≠ y ∧ x ^ 2 + b * x + c = 0 ∧ y ^ 2 + b * y + c = 0)
(h2 : ∃ x y, x ≠ y ∧ x ^ 2 + b * x - c = 0 ∧ y ^ 2 + b * y - c = 0) : (∃ p q : ℤ, p > 0 ∧ q > 0 ∧ p ≠ q ∧ 2 * b ^ 2 = p ^ 2 + q ^ 2) ∧
(∃ r s : ℤ, r > 0 ∧ s > 0 ∧ r ≠ s ∧ b ^ 2 = r ^ 2 + s ^ 2):= by
  -- Extract the solutions from the hypotheses
  rcases h1 with ⟨p, q, hpq, hp, hq⟩
  rcases h2 with ⟨r, s, hrs, hr, hs⟩

  -- Prove that b² - 4c = (p-q)²
  -- This comes from the quadratic formula for the first equation
  have h1 : b ^ 2 - 4 * c = (p - q) ^ 2:= by
    -- Show that (p-q)(p+q+b) = 0
    have g1 : (p - q) * (p + q + b) = 0:= by linarith
    simp at g1
    rcases g1 with g1 | g1
    .
      -- If p-q = 0, then p = q, which contradicts our assumption
      replace g1 : p = q:= by linarith
      trivial
    .
      -- If p+q+b = 0, then b = -(p+q)
      replace g1 : b = -(p + q):= by linarith
      subst b
      ring_nf at hp
      linarith

  -- Prove that b² + 4c = (r-s)²
  -- This comes from the quadratic formula for the second equation
  have h2 : b ^ 2 + 4 * c = (r - s) ^ 2:= by
    -- Show that (r-s)(r+s+b) = 0
    have g1 : (r - s) * (r + s + b) = 0:= by linarith
    simp at g1
    rcases g1 with g1 | g1
    .
      -- If r-s = 0, then r = s, which contradicts our assumption
      replace g1 : r = s:= by linarith
      trivial
    .
      -- If r+s+b = 0, then b = -(r+s)
      replace g1 : b = -(r + s):= by linarith
      subst b
      ring_nf at hr
      linarith

  -- Now prove both parts of the theorem
  constructor
  .
    -- Part (i): Find positive integers p and q such that 2b² = p² + q²
    -- Use |p-q| and |r-s| as our candidates
    use |p - q|, |r - s|
    refine ⟨?_, ?_, ?_, ?_⟩
    .
      -- Prove |p-q| > 0
      by_contra H
      simp at H
      replace H : p = q:= by linarith
      trivial
    .
      -- Prove |r-s| > 0
      by_contra H
      simp at H
      replace H : r = s:= by linarith
      trivial
    .
      -- Prove |p-q| ≠ |r-s|
      by_contra H
      replace H : (p - q) ^ 2 = (r - s) ^ 2:= by exact (sq_eq_sq_iff_abs_eq_abs (p - q) (r - s)).mpr H
      replace H : c = 0:= by linarith
      trivial
    .
      -- Prove 2b² = |p-q|² + |r-s|²
      rw [show |p - q| ^ 2 = (p - q) ^ 2 by norm_num]
      rw [show |r - s| ^ 2 = (r - s) ^ 2 by norm_num]
      linarith
  .
    -- Part (ii): Find positive integers r and s such that b² = r² + s²
    -- Define A = p-q and B = r-s for convenience
    set A:= p - q with hA
    set B:= r - s with hB
    clear_value A B

    -- From part (i), we know 2b² = A² + B²
    have h3 : 2 * b ^ 2 = A ^ 2 + B ^ 2:= by linarith

    -- Note that 2b² is always even
    replace g3 : Even (2 * b ^ 2):= by exact even_two_mul (b ^ 2)

    -- Case analysis based on whether A is odd or even
    by_cases g1 : Odd A
    .
      -- Case 1: A is odd
      -- Then B must also be odd for A² + B² to be even
      have g2 : Odd B:= by
        by_contra H
        simp at H
        replace g1 : Odd (A ^ 2):= by exact Odd.pow g1
        replace H : Even (B ^ 2):= by refine (Int.even_pow' (by omega)).mpr H
        have g2 : Odd (A ^ 2 + B ^ 2):= by exact Even.odd_add H g1
        absurd g2
        simp
        rw [←h3]
        exact g3

      -- Since A and B are odd, write A = 2p1+1 and B = 2q1+1
      simp [Odd] at g1 g2
      rcases g1 with ⟨p1, hp1⟩
      rcases g2 with ⟨q1, hq1⟩

      -- Use |p1+q1+1| and |p1-q1| as our candidates
      use |p1 + q1 + 1|, |p1 - q1|
      refine ⟨?_, ?_, ?_, ?_⟩
      .
        -- Prove |p1+q1+1| > 0
        by_contra H
        simp at H
        replace H : A = -B:= by linarith
        replace H : A ^ 2 = (-B) ^ 2:= by rw [H]
        replace H : c = 0:= by linarith
        trivial
      .
        -- Prove |p1-q1| > 0
        by_contra H
        simp at H
        replace H : A = B:= by linarith
        replace H : A ^ 2 = B ^ 2:= by rw [H]
        replace H : c = 0:= by linarith
        trivial
      .
        -- Prove |p1+q1+1| ≠ |p1-q1|
        by_contra H
        replace H : (p1 + q1 + 1) ^ 2 = (p1 - q1) ^ 2:= by exact (sq_eq_sq_iff_abs_eq_abs (p1 + q1 + 1) (p1 - q1)).mpr H
        replace H : A * B = 0:= by rw [hp1, hq1] ; linarith
        rw [hA, hB] at H
        simp at H
        rcases H with H | H
        .
          replace H : p = q:= by linarith
          trivial
        .
          replace H : r = s:= by linarith
          trivial
      .
        -- Prove b² = |p1+q1+1|² + |p1-q1|²
        norm_num
        rw [hp1, hq1] at h3
        linarith
    .
      -- Case 2: A is even
      -- Then B must also be even for A² + B² to be even
      simp at g1
      have g2 : Even B:= by
        by_contra H
        simp at H
        replace g1 : Even (A ^ 2):= by refine (Int.even_pow' (by omega)).mpr g1
        replace H : Odd (B ^ 2):= by exact Odd.pow H
        have g2 : Odd (A ^ 2 + B ^ 2):= by exact Even.add_odd g1 H
        absurd g2
        simp
        rw [←h3]
        exact g3

      -- Since A and B are even, write A = 2p1 and B = 2q1
      simp [Even] at g1 g2
      rcases g1 with ⟨p1, hp1⟩
      rcases g2 with ⟨q1, hq1⟩
      ring_nf at hp1 hq1

      -- Use |p1-q1| and |p1+q1| as our candidates
      use |p1 - q1|, |p1 + q1|
      refine ⟨?_, ?_, ?_, ?_⟩
      .
        -- Prove |p1-q1| > 0
        by_contra H
        simp at H
        replace H : A = B:= by linarith
        replace H : A ^ 2 = B ^ 2:= by rw [H]
        replace H : c = 0:= by linarith
        trivial
      .
        -- Prove |p1+q1| > 0
        by_contra H
        simp at H
        replace H : A = -B:= by linarith
        replace H : A ^ 2 = (-B) ^ 2:= by rw [H]
        replace H : c = 0:= by linarith
        trivial
      .
        -- Prove |p1-q1| ≠ |p1+q1|
        by_contra H
        replace H : (p1 - q1) ^ 2 = (p1 + q1) ^ 2:= by exact (sq_eq_sq_iff_abs_eq_abs (p1 - q1) (p1 + q1)).mpr H
        replace H : A * B = 0:= by rw [hp1, hq1] ; linarith
        rw [hA, hB] at H
        simp at H
        rcases H with H | H
        .
          replace H : p = q:= by linarith
          trivial
        .
          replace H : r = s:= by linarith
          trivial
      .
        -- Prove b² = |p1-q1|² + |p1+q1|²
        norm_num
        rw [hp1, hq1] at h3
        linarith
