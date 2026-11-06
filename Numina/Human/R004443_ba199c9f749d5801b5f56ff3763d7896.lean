import Mathlib

/- Example 1 Find all positive integer solutions $(x, y)$ for $\left|12^{x}-5^{y}\right|=7$.
-/

-- lemma that a^m = a^n then m = n in Nats
lemma l_pow_right_inj (ha : 1 < a) : a ^ m = a ^ n ↔ m = n := by
  simp [Nat.le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

-- modulo 4, 5^y - 12^x ≠ 7 when 0 < x
lemma l_eqn_mod_four {x y : ℕ} (hx : 0 < x) : 5 ^ y - 12 ^ x ≠ (7 : ZMod 4) := by
  rw [show (5 : ZMod 4) = 1 by norm_cast, show (12 : ZMod 4) = 0 by norm_cast,
    show (7 : ZMod 4) = 3 by norm_cast]
  rw [zero_pow (by omega)]
  simp
  norm_cast

-- 12^x - 5^y = 7 means y is Odd, proven by taking modulo 3
lemma l_eqn_mod_three {x y : ℕ} (hx : 0 < x) (h : 12 ^ x - 5 ^ y = (7 : ℤ)) : Odd y := by
  replace h : 12 ^ x - 5 ^ y = (7 : ZMod 3) := by
    norm_cast at h ⊢
    rw [h]
    norm_cast
  rw [show (12 : ZMod 3) = 0 by norm_cast, show (5 : ZMod 3) = -1 by norm_cast,
    show (7 : ZMod 3) = 1 by norm_cast, zero_pow (by omega)] at h
  simp at h
  obtain hy | hy := Nat.even_or_odd y
  . rw [hy.neg_one_pow] at h
    norm_cast at h
  . assumption

-- 12 ^ x - 5 ^ y ≠ 7 modulo 8 when 1 < x and y odd
lemma l_eqn_mod_twelve {x y : ℕ} (hx : 1 < x) (hy : Odd y) : 12 ^ x - 5 ^ y ≠ (7 : ZMod 8) := by
  obtain ⟨k, hk⟩ := hy
  rw [hk, show x = (x - 2) + 2 by omega, pow_add, pow_add, pow_mul]
  norm_num
  rw [show (144 : ZMod 8) = 0 by norm_cast, show (25 : ZMod 8) = 1 by norm_cast]
  norm_num
  norm_cast

theorem number_theory_267573 (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    |(12 ^ x : ℤ) - 5 ^ y| = 7 ↔ (x, y) = (1, 1) := by
  constructor
  . rintro h
    -- x ≤ 1 or 1 < x
    obtain hx | hx := le_or_gt x 1
    -- for x ≤ 1, we have x = 1
    . replace hx : x = 1 := by omega
      rw [hx] at h ⊢
      -- the absolute value is self or negative
      obtain h' | h' := abs_choice (12 ^ 1 - 5 ^ y : ℤ)
      -- if self, then we have 5^y = 5^1 so y = 1
      . rw [h'] at h
        replace h : 5^y = 5^1 := by linarith
        rw [l_pow_right_inj (by norm_num)] at h
        simp [h]
      -- if negative then 5^1 < 5^y < 5^2 not possible
      . rw [h'] at h
        replace h : 5^y = 19 := by linarith
        have h1 : 5^y < 5^2 := by linarith
        have h2 : 5^1 < 5^y := by linarith
        rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h1 h2
        omega
    -- for 1 < x, absolute vlaue is positive or negative
    . obtain h' | h' := abs_choice (12 ^ x - 5 ^ y : ℤ)
      -- if positive, then by lemma y is odd, and then by lemma modulo 8 we get contradiction
      . rw [h'] at h
        have hy := l_eqn_mod_three (by assumption) h
        replace h : 12 ^ x - 5 ^ y = (7 : ZMod 8) := by
          rw_mod_cast [h]
          norm_cast
        exfalso
        apply l_eqn_mod_twelve (by assumption) (by assumption) h
      -- if negative then by lemma, modulo 4 we get contradiction
      . rw [h'] at h
        ring_nf at h
        replace h : 5 ^ y - 12 ^ x = (7 : ZMod 4) := by
          norm_cast at h ⊢
          rw [h]
          norm_cast
        exfalso
        apply l_eqn_mod_four (by assumption) h
  -- other direction, plug in x, y and we're done.
  . rintro ⟨rfl, rfl⟩
    norm_num