import Mathlib
/- Example 5 Find all positive integers $x>1, y>1, z>1$, such that
$$1!+2!+\cdots+x!=y^{z}$$ -/
theorem number_theory_7986 : {(x, y, z) : ℕ × ℕ × ℕ | x > 1 ∧ y > 1 ∧ z > 1 ∧ (∑ i in Finset.range x, (i + 1).factorial = y ^ z)} = {(3, 3, 2)}:= by
  -- We use extensionality to prove equality of sets
  ext ⟨x, y, z⟩
  constructor
  -- Forward direction: if (x,y,z) satisfies the equation, then (x,y,z) = (3,3,2)
  .
    intro h
    simp at h
    rcases h with ⟨hx, hy, hz, h⟩
    -- First we prove that 3 divides y
    have h2 : 3 ∣ y:= by
      have g1 : Nat.Prime 3:= by decide
      -- If 3 divides y^z, then 3 divides y (by property of prime numbers)
      suffices 3 ∣ y ^ z by exact Nat.Prime.dvd_of_dvd_pow g1 this
      rw [←h]
      set a:= x - 2 with ha
      clear_value a
      replace ha : x = a + 2:= by omega
      subst x
      clear hx h
      -- Induction on a to prove that 3 divides the sum for any x ≥ 2
      induction a with
      | zero =>
        simp [Finset.sum_range_succ, Nat.factorial_succ]
      | succ a ih =>
        rw [show a + 1 + 2 = (a + 2) + 1 by ring]
        rw [Finset.sum_range_succ]
        by_cases ha : a = 0
        -- Case a = 0
        .
          subst a
          simp [Finset.sum_range_succ, Nat.factorial_succ]
          omega
        -- Case a > 0
        .
          suffices 3 ∣ (a + 2 + 1).factorial by exact (Nat.dvd_add_iff_right ih).mp this
          suffices a + 2 + 1 > 3 by refine Nat.dvd_factorial (by omega) (by omega)
          omega
    -- Case analysis based on the value of x
    by_cases h1 : x ≤ 7
    -- Case x ≤ 7: we check each possible value of x
    .
      replace h1 : x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7:= by omega
      rcases h2 with ⟨k, hk⟩
      subst y
      replace hy : k > 0:= by omega
      set w:= z - 2 with hw
      clear_value w
      replace hw : z = w + 2:= by omega
      subst z
      clear hz
      -- 9 divides the sum for any x
      have h2 : 9 ∣ ∑ i ∈ Finset.range x, (i + 1).factorial:= by
        rw [h]
        ring_nf
        simp
      -- Check each possible value of x from 2 to 7
      rcases h1 with h1 | h1 | h1 | h1 | h1 | h1
      -- Case x = 2
      .
        subst x
        simp [Finset.sum_range_succ, Nat.factorial_succ] at h2
        omega
      -- Case x = 3
      .
        subst x
        simp [Finset.sum_range_succ, Nat.factorial_succ] at h
        ring_nf at h
        replace h : 1 = k ^ 2 * k ^ w * 3 ^ w:= by omega
        -- Prove that k = 1
        have hk : k = 1:= by
          by_contra H
          replace H : k ≥ 2:= by omega
          rw [show k ^ 2 * k ^ w * 3 ^ w = k * k ^ w * 3 ^ w * k by ring] at h
          have g1 : k * k ^ w * 3 ^ w > 0:= by positivity
          replace g1 : k * k ^ w * 3 ^ w ≥ 1:= by omega
          replace g1 : k * k ^ w * 3 ^ w * k ≥ 1 * 2:= by exact Nat.mul_le_mul g1 H
          linarith
        subst k
        simp at h
        -- Prove that w = 0
        replace h : w = 0:= by
          by_contra H
          replace H : w ≥ 1:= by omega
          replace H : 3 ^ w ≥ 3 ^ 1:= by exact Nat.pow_le_pow_of_le hx H
          linarith
        subst w
        simp
      -- Case x = 4
      .
        subst x
        simp [Finset.sum_range_succ, Nat.factorial_succ] at h2
        omega
      -- Case x = 5
      .
        subst x
        simp [Finset.sum_range_succ, Nat.factorial_succ] at h
        ring_nf at h
        replace h : 17 = k ^ 2 * k ^ w * 3 ^ w:= by omega
        -- Prove that w = 0
        have hw : w = 0:= by
          by_contra H
          replace H : w ≥ 1:= by omega
          set t:= w - 1 with ht
          clear_value t
          replace ht : w = t + 1:= by omega
          subst w
          ring_nf at h
          replace h : 3 ∣ 17:= by rw [h] ; simp
          omega
        subst w
        simp at h
        -- Show that k must be at least 5, which leads to a contradiction
        have hk1 : k > 4:= by
          by_contra H
          simp at H
          replace H : k ^ 2 ≤ 4 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
          linarith
        replace hk1 : k ≥ 5:= by omega
        replace hk1 : k ^ 2 ≥ 5 ^ 2:= by exact Nat.pow_le_pow_of_le_left hk1 2
        linarith
      -- Case x = 6
      .
        subst x
        simp [Finset.sum_range_succ, Nat.factorial_succ] at h
        ring_nf at h
        replace h : 97 = k ^ 2 * k ^ w * 3 ^ w:= by omega
        -- Prove that w = 0
        have hw : w = 0:= by
          by_contra H
          replace H : w ≥ 1:= by omega
          set t:= w - 1 with ht
          clear_value t
          replace ht : w = t + 1:= by omega
          subst w
          ring_nf at h
          replace h : 3 ∣ 97:= by rw [h] ; simp
          omega
        subst w
        simp at h
        -- Show that k must be at least 10, which leads to a contradiction
        have hk1 : k > 9:= by
          by_contra H
          simp at H
          replace H : k ^ 2 ≤ 9 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
          linarith
        replace hk1 : k ≥ 10:= by omega
        replace hk1 : k ^ 2 ≥ 10 ^ 2:= by exact Nat.pow_le_pow_of_le_left hk1 2
        linarith
      -- Case x = 7
      .
        subst x
        simp [Finset.sum_range_succ, Nat.factorial_succ] at h
        -- Use the fact that 73 is prime to derive a contradiction
        have g1 : Nat.Prime 73:= by decide
        have g2 : 73 ∣ (3 * k) ^ (w + 2):= by rw [←h] ; omega
        replace g2 : 73 ∣ 3 * k:= by exact Nat.Prime.dvd_of_dvd_pow g1 g2
        rcases g2 with ⟨t, ht⟩
        rw [ht] at h
        ring_nf at h
        replace h : 5329 ∣ 5913:= by rw [h] ; simp
        omega
    -- Case x ≥ 8
    .
      simp at h1
      replace h1 : x ≥ 8:= by omega
      -- Prove that z = 2
      have h3 : z = 2:= by
        set a:= x - 8 with ha
        clear_value a
        replace ha : x = a + 8:= by omega
        subst x
        clear hx h1
        -- Show that 27 doesn't divide y^z if z ≥ 3
        have g1 : ¬(27 ∣ y ^ z):= by
          -- Prove that 27 divides (x+9)! for any x
          have h1 : ∀ x : ℕ, 27 ∣ (x + 9).factorial:= by
            intro x
            induction x with
            | zero =>
              simp [Nat.factorial_succ]
              omega
            | succ x ih =>
              rw [show x + 1 + 9 = (x + 9) + 1 by ring]
              rw [Nat.factorial_succ]
              set t:= (x + 9).factorial
              clear_value t
              set s:= x + 9 + 1
              clear_value s
              exact Dvd.dvd.mul_left ih s
          rw [←h]
          clear h
          -- Induction on a to show that 27 doesn't divide the sum
          induction a with
          | zero =>
            simp [Finset.sum_range_succ, Nat.factorial_succ]
            omega
          | succ a ih =>
            by_contra H
            rw [show a + 1 + 8 = (a + 8) + 1 by ring] at H
            rw [Finset.sum_range_succ] at H
            rw [show a + 8 + 1 = a + 9 by ring] at H
            specialize h1 a
            replace H : 27 ∣ ∑ x ∈ Finset.range (a + 8), (x + 1).factorial:= by exact (Nat.dvd_add_iff_left h1).mpr H
            trivial
        -- Derive a contradiction if z ≥ 3
        by_contra H
        set w:= z - 3 with hw
        clear_value w
        replace hw : z = w + 3:= by omega
        subst z
        clear hz
        have h3 : 27 ∣ y ^ (w + 3):= by
          rcases h2 with ⟨k, hk⟩
          subst y
          ring_nf
          simp
        trivial
      subst z
      simp
      clear h2 hz
      set a:= x - 8 with ha
      clear_value a
      replace ha : x = a + 8:= by omega
      subst x
      clear h1 hx
      -- Use modular arithmetic to show that y = 3
      -- Prove that the sum is congruent to 3 modulo 5 for any x ≥ 5
      have h1 : ∀ x : ℕ, ∑ i ∈ Finset.range (x + 5), (i + 1).factorial ≡ 3 [MOD 5]:= by
        intro x
        induction x with
        | zero =>
          simp [Finset.sum_range_succ, Nat.factorial_succ]
          rfl
        | succ x ih =>
          rw [show x + 1 + 5 = (x + 5) + 1 by ring]
          rw [Finset.sum_range_succ]
          rw [show 3 = 3 + 0 by ring]
          suffices (x + 5 + 1).factorial ≡ 0 [MOD 5] by exact Nat.ModEq.add ih this
          suffices 5 ∣ (x + 5 + 1).factorial by exact Nat.modEq_zero_iff_dvd.mpr this
          suffices x + 5 + 1 > 5 by refine Nat.dvd_factorial (by omega) (by omega)
          omega
      specialize h1 (a + 3)
      rw [show a + 3 + 5 = a + 8 by ring] at h1
      rw [h] at h1
      -- Check all possible values of y modulo 5
      mod_cases y % 5
      all_goals
        replace H:= Nat.ModEq.pow 2 H
        replace H:= Nat.ModEq.trans (id (Nat.ModEq.symm h1)) H
        simp [Nat.ModEq] at H
  -- Reverse direction: if (x,y,z) = (3,3,2), then it satisfies the equation
  .
    intro h
    simp at h
    rcases h with ⟨hx, hy, hz⟩
    subst x y z
    simp [Finset.sum_range_succ, Nat.factorial_succ]
