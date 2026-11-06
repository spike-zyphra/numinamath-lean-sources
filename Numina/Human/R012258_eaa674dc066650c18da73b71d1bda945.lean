import Mathlib
/- Нека је $a$ природан број такав да за сваки природан број $n$ број $n^{2} a-1$ има бар један делилац већи од 1 који даје остатак 1 при дељењу са $n$. Доказати да је $а$ потпун квадрат.

(Душан Ђукић) -/
theorem number_theory_608111 (a : ℕ) (ha : ∀ n : ℕ, ∃ d : ℕ, d > 1 ∧ d ∣ n ^ 2 * a - 1 ∧ d ≡ 1 [MOD n]) : IsSquare a:= by
  -- Set n = 2a + 2 for our specific choice
  set n:= 2 * a + 2 with hn
  clear_value n
  -- Apply the hypothesis to our chosen n
  specialize ha n
  -- Extract the divisor d and its properties
  rcases ha with ⟨d, hd, h1, h2⟩
  -- Show that d ≥ 1
  have g1 : d ≥ 1:= by omega
  -- Convert the modular equivalence to divisibility
  replace h2 : n ∣ d - 1:= by exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm h2))
  -- Express d in terms of n and some k
  rcases h2 with ⟨k, hk⟩
  replace hk : d = n * k + 1:= by omega
  -- Extract the quotient s from the divisibility condition
  rcases h1 with ⟨s, hs⟩
  -- Case analysis: a = 0 or a ≠ 0
  by_cases ha : a = 0
  .
    -- If a = 0, then a is trivially a perfect square (0 = 0²)
    subst a
    simp
  .
    -- Case where a ≠ 0
    have hane:= ha
    -- Show that n²a > 0
    replace ha : n ^ 2 * a > 0:= by subst n ; positivity
    -- Rewrite the divisibility condition as an equation
    replace hs : n ^ 2 * a = d * s + 1:= by omega
    clear ha
    -- Substitute the expression for d
    subst d
    ring_nf at hs
    -- Show that k > 0
    have hkpos : k > 0:= by
      by_contra H
      simp at H
      subst k
      simp at hd
    -- Rearrange the equation
    rw [show 1 + n * k * s + s = k * s * n + (s + 1) by ring] at hs
    rw [show n ^ 2 * a = a * n * n by ring] at hs
    -- Show that n divides the right side
    have h1 : n ∣ k * s * n + (s + 1):= by rw [←hs] ; simp
    -- Show that n divides k * s * n
    have h2 : n ∣ k * s * n:= by simp
    -- Therefore n divides s + 1
    replace h1 : n ∣ s + 1:= by exact (Nat.dvd_add_iff_right h2).mpr h1
    -- Express s + 1 in terms of n and some t
    rcases h1 with ⟨t, ht⟩
    -- Derive a key equation
    replace hs : k * n + a * n ^ 2 = (s + 1) * (k * n + 1):= by linarith
    -- Substitute the expression for s + 1
    rw [ht] at hs
    -- Factor out n from both sides
    rw [show k * n + a * n ^ 2 = n * (k + a * n) by ring] at hs
    rw [show n * t * (k * n + 1) = n * (t * (k * n + 1)) by ring] at hs
    -- Show that n > 0
    have hn1 : n > 0:= by omega
    -- Cancel n from both sides
    replace hs : (k + a * n) = t * (k * n + 1):= by exact Nat.eq_of_mul_eq_mul_left hn1 hs
    ring_nf at hs
    clear g1 hd
    -- Show that t > 0
    have ht1 : t > 0:= by
      by_contra H
      simp at H
      subst t
      simp at hs
      rcases hs with ⟨_, h2⟩
      rcases h2 with h2 | _
      .
        trivial
      .
        linarith
    -- Establish an upper bound for k * t
    have h1 : k * t ≤ 2 * a:= by
      replace ht1 : n * t ≥ 2:= by
        replace hn : n ≥ 2:= by omega
        exact le_mul_of_le_of_one_le hn ht1
      replace ht1 : k * (n * t) ≥ k * 2:= by exact Nat.mul_le_mul_left k ht1
      replace ht1 : k * t * n ≤ 2 * a * n:= by linarith
      exact Nat.le_of_mul_le_mul_right ht1 hn1
    -- Show that a = k * t
    replace h2 : a = k * t:= by
      by_contra H
      replace H : a < k * t ∨ a > k * t:= by exact Nat.lt_or_gt_of_ne H
      rcases H with H | H
      .
        -- Case: a < k * t leads to contradiction
        replace H : a + 1 ≤ k * t:= by omega
        replace H : (a + 1) * n ≤ k * t * n:= by exact Nat.mul_le_mul_right n H
        have g1 : k ≤ k * t:= by exact Nat.le_mul_of_pos_right k ht1
        linarith
      .
        -- Case: a > k * t leads to contradiction
        replace H : a ≥ k * t + 1:= by omega
        replace H : a * n ≥ (k * t + 1) * n:= by exact Nat.mul_le_mul_right n H
        have g1 : t ≤ k * t:= by refine Nat.le_mul_of_pos_left t hkpos
        linarith
    -- Substitute a = k * t
    subst a
    -- Show that k = t
    replace hs : k = t:= by linarith
    -- Substitute k = t, so a = t²
    subst k
    simp
