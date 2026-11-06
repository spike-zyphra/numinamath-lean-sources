import Mathlib
/- 21. If the polynomial $x^{2}-(a+4) x+3 a-4$ (where $a>0$) can be factored into the product of two linear factors $(x+b),(x+c)$ (where $b, c$ are integers), then $a=$ $\qquad$ -/
theorem number_theory_207190 (a : ℝ) (ha : a > 0) : (∃ b c : ℤ, ∀ x : ℝ, x ^ 2 - (a + 4) * x + (3 * a - 4) = (x + b) * (x + c)) ↔ a = 8:= by
  constructor
  -- Forward direction: if the polynomial can be factored, then a = 8
  .
    intro h
    -- Extract the integer coefficients b and c from the factorization
    rcases h with ⟨b, c, h⟩
    -- Evaluate the polynomial equation at x = 0
    have h1:= h 0
    -- Evaluate the polynomial equation at x = 1
    have h2:= h 1
    simp at h1 h2
    -- From Vieta's formulas: sum of roots equals -(coefficient of x)
    replace h3 : b + c = -a - 4:= by linarith
    -- Derive a constraint equation by combining h1 and h2
    replace h4 : 3 * b + 3 * c + b * c + 16 = 0:= by rify ; linarith
    -- Simplify to get (b+3)(c+3) = -7
    replace h4 : (b + 3) * (c + 3) = -7:= by linarith
    -- Since b and c are integers, (b+3) must divide 7
    have h5 : (b + 3).natAbs ∣ 7:= by
      zify
      suffices b + 3 ∣ 7 by exact (abs_dvd (b + 3) 7).mpr this
      replace h4 : 7 = (b + 3) * (-c - 3):= by linarith
      rw [h4]
      simp
    -- 7 is prime
    have g1 : Nat.Prime 7:= by norm_num
    -- The absolute value of (b+3) must be 1 or 7
    replace h5 : (b + 3).natAbs = 1 ∨ (b + 3).natAbs = 7:= by exact (Nat.dvd_prime g1).mp h5
    rcases h5 with h5 | h5
    -- Case 1: |b+3| = 1
    .
      zify at h5
      -- This means b+3 = ±1
      replace h5 : b + 3 = 1 ∨ b + 3 = -1:= by exact abs_eq_abs.mp h5
      rcases h5 with h5 | h5
      -- Subcase 1a: b+3 = 1, so b = -2
      .
        rw [h5] at h4
        -- From (b+3)(c+3) = -7, we get c = -10
        replace h4 : c = -10:= by linarith
        replace h5 : b = -2:= by linarith
        subst b c
        simp at h1
        -- This gives us a = 8
        linarith
      -- Subcase 1b: b+3 = -1, so b = -4
      .
        rw [h5] at h4
        -- From (b+3)(c+3) = -7, we get c = 4
        replace h4 : c = 4:= by linarith
        replace h5 : b = -4:= by linarith
        subst b c
        simp at h1
        -- This also gives us a = 8
        linarith
    -- Case 2: |b+3| = 7
    .
      zify at h5
      -- This means b+3 = ±7
      replace h5 : b + 3 = 7 ∨ b + 3 = -7:= by exact abs_eq_abs.mp h5
      rcases h5 with h5 | h5
      -- Subcase 2a: b+3 = 7, so b = 4
      .
        rw [h5] at h4
        -- From (b+3)(c+3) = -7, we get c = -4
        replace h4 : c = -4:= by linarith
        replace h5 : b = 4:= by linarith
        subst b c
        simp at h1
        -- This gives us a = 8
        linarith
      -- Subcase 2b: b+3 = -7, so b = -10
      .
        rw [h5] at h4
        -- From (b+3)(c+3) = -7, we get c = -2
        replace h4 : c = -2:= by linarith
        replace h5 : b = -10:= by linarith
        subst b c
        simp at h1
        -- This also gives us a = 8
        linarith
  -- Backward direction: if a = 8, then the polynomial can be factored
  .
    intro h
    subst a
    -- Use b = -2 and c = -10 as the factorization
    use -2, -10
    intro x
    simp
    -- Verify that x² - 12x + 20 = (x - 2)(x - 10)
    linarith
