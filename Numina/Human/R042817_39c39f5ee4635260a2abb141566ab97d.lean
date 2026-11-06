import Mathlib
/- Find all 4-digit integers of the form $a a b b$ (when written in base 10) that are perfect squares. -/
theorem number_theory_608715 (a b : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9) : (∃ k : ℕ, a * 10 ^ 3 + a * 10 ^ 2 + b * 10 ^ 1 + b * 10 ^ 0 = k ^ 2) ↔ (a = 7 ∧ b = 4):= by
  constructor
  -- Forward direction: if aabb is a perfect square, then a=7 and b=4
  .
    intro h
    rcases h with ⟨k, hk⟩
    simp at hk
    ring_nf at hk
    -- Rewrite aabb as 11*(100a + b) to identify divisibility by 11
    rw [show a * 1100 + b * 11 = 11 * (a * 100 + b) by omega] at hk
    -- Prove that 11 is prime
    have h1 : Nat.Prime 11 := by norm_num
    -- If 11 divides k², then 11 divides k
    have h2 : 11 ∣ k ^ 2 := by rw [←hk] ; simp
    replace h2 : 11 ∣ k:= by exact Nat.Prime.dvd_of_dvd_pow h1 h2
    replace h2 : ∃ t : ℕ, k = 11 * t:= by exact h2
    rcases h2 with ⟨t, ht⟩
    subst k
    -- Derive that a*100 + b = 11*t²
    replace hk : a * 100 + b = 11 * t ^ 2:= by linarith
    have h2 : 11 ∣ a * 100 + b:= by rw [hk] ; simp
    -- Rewrite to isolate a+b
    rw [show a * 100 + b = 11 * (9 * a) + (a + b) by ring] at h2
    have h3 : 11 ∣ 11 * (9 * a):= by simp
    -- Prove that 11 divides a+b
    replace h2 : 11 ∣ a + b:= by exact (Nat.dvd_add_iff_right h3).mpr h2
    clear h3
    replace h2 : ∃ s : ℕ, a + b = 11 * s:= by exact h2
    rcases h2 with ⟨s, hs⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    -- Since a ≤ 9 and b ≤ 9, a+b ≤ 18, so s must be 1
    have hs1 : s = 1:= by omega
    subst s
    simp at hs
    -- List all possible values for a given the constraints
    have g1 : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9:= by omega
    -- Express b in terms of a
    replace hs : b = 11 - a:= by omega
    subst b
    -- Check each possible value of a
    rcases g1 with g1 | g1 | g1 | g1 | g1 | g1 | g1 | g1
    -- Case a=2, b=9
    .
      subst a
      simp at hk
      -- Prove t must be greater than 4
      have ht1 : t > 4:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 4 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      -- Prove t must be less than 5
      have ht2 : t < 5:= by
        by_contra H
        simp at H
        replace H : 5 ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case a=3, b=8
    .
      subst a
      simp at hk
      have ht1 : t > 5:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 5 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have ht2 : t < 6:= by
        by_contra H
        simp at H
        replace H : 6 ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case a=4, b=7
    .
      subst a
      simp at hk
      have ht1 : t > 6:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have ht2 : t < 7:= by
        by_contra H
        simp at H
        replace H : 7 ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case a=5, b=6
    .
      subst a
      simp at hk
      have ht1 : t > 6:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 6 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have ht2 : t < 7:= by
        by_contra H
        simp at H
        replace H : 7 ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case a=6, b=5
    .
      subst a
      simp at hk
      have ht1 : t > 7:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 7 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have ht2 : t < 8:= by
        by_contra H
        simp at H
        replace H : 8 ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case a=7, b=4
    .
      subst a
      simp
    -- Case a=8, b=3
    .
      subst a
      simp at hk
      have ht1 : t > 8:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 8 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have ht2 : t < 9:= by
        by_contra H
        simp at H
        replace H : 9 ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
    -- Case a=9, b=2
    .
      subst a
      simp at hk
      have ht1 : t > 9:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 9 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      have ht2 : t < 10:= by
        by_contra H
        simp at H
        replace H : 10 ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
        linarith
      linarith
  -- Reverse direction: if a=7 and b=4, then aabb is a perfect square
  .
    intro h
    rcases h with ⟨h1, h2⟩
    subst a b
    simp
    -- Show that 7744 = 88²
    use 88
    simp
