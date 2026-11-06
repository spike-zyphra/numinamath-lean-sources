import Mathlib
/- Find all positive integer solutions $ x, y, z$ of the equation $ 3^x \plus{} 4^y \equal{} 5^z.$ -/
theorem number_theory_34637 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : 3 ^ x + 4 ^ y = 5 ^ z ↔ x = 2 ∧ y = 2 ∧ z = 2:= by
  constructor
  .
    -- Forward direction: if 3^x + 4^y = 5^z, then x = y = z = 2
    intro h
    zify at h
    -- First, prove that z must be even
    have h1 : Even z:= by
      -- Show that 5^z ≡ 1 (mod 3)
      have h2 : 5 ^ z ≡ 1 [ZMOD 3] := by
        replace h : 3 ^ x + 4 ^ y ≡ 5 ^ z [ZMOD 3]:= by rw [h]
        have g1 : 3 ≡ 0 [ZMOD 3]:= by exact rfl
        replace g1 : 3 ^ x ≡ 0 ^ x [ZMOD 3]:= by exact Int.ModEq.pow x g1
        rw [show (0 : ℤ) ^ x = 0 by exact Mathlib.Tactic.Ring.zero_pow hx] at g1
        have g2 : 4 ≡ 1 [ZMOD 3]:= by exact rfl
        replace g2 : 4 ^ y ≡ 1 ^ y [ZMOD 3]:= by exact Int.ModEq.pow y g2
        simp at g2
        replace g1 : 3 ^ x + 4 ^ y ≡ 0 + 1 [ZMOD 3]:= by exact Int.ModEq.add g1 g2
        simp at g1
        exact Int.ModEq.trans (id (Int.ModEq.symm h)) g1
      -- Since 5 ≡ -1 (mod 3), we have 5^z ≡ (-1)^z (mod 3)
      have h3 : 5 ≡ -1 [ZMOD 3]:= by exact rfl
      replace h3 : 5 ^ z ≡ (-1) ^ z [ZMOD 3]:= by exact Int.ModEq.pow z h3
      replace h2 : (-1) ^ z ≡ 1 [ZMOD 3]:= by exact Int.ModEq.trans (id (Int.ModEq.symm h3)) h2
      -- If z is odd, then (-1)^z = -1, which leads to a contradiction
      by_contra h4
      simp at h4
      rw [show (-1 : ℤ) ^ z = -1 by exact Odd.neg_one_pow h4] at h2
      replace h2 : 1 + -1 ≡ 1 + 1 [ZMOD 3]:= by exact Int.ModEq.add rfl h2
      simp at h2
      replace h2 : (3 : ℤ) ∣ 2:= by exact Int.dvd_of_emod_eq_zero (id (Int.ModEq.symm h2))
      omega
    -- Since z is even, we can write z = 2*z1
    replace h1 : 2 ∣ z:= by exact even_iff_two_dvd.mp h1
    replace h1 : ∃ z1 : ℕ, z = 2 * z1:= by exact h1
    rcases h1 with ⟨z1, h1⟩
    rw [h1] at h
    rw [show 2 * z1 = z1 * 2 by ring] at h
    -- Rewrite the equation using the fact that z is even
    rw [show (5 : ℤ) ^ (z1 * 2) = (5 ^ z1) ^ 2 by exact pow_mul 5 z1 2] at h
    rw [show (4 : ℤ) = 2 ^ 2 by omega] at h
    rw [show ((2 : ℤ) ^ 2) ^ y = 2 ^ (2 * y) by exact Eq.symm (pow_mul 2 2 y)] at h
    rw [show 2 * y = y * 2 by ring] at h
    rw [show (2 : ℤ) ^ (y * 2) = (2 ^ y) ^ 2 by exact pow_mul 2 y 2] at h
    -- Factor the equation: (5^z1 - 2^y)(5^z1 + 2^y) = 3^x
    replace h : ((5 : ℤ) ^ z1 - 2 ^ y) * (5 ^ z1 + 2 ^ y) = 3 ^ x:= by linarith
    -- Both factors must divide 3^x
    have g1 : (5 : ℤ) ^ z1 - 2 ^ y ∣ 3 ^ x:= by exact Dvd.intro (5 ^ z1 + 2 ^ y) h
    have g2 : (5 : ℤ) ^ z1 + 2 ^ y ∣ 3 ^ x:= by exact Dvd.intro_left (5 ^ z1 - 2 ^ y) h
    have g3 : Nat.Prime 3:= by native_decide
    -- Convert to natural numbers for divisibility analysis
    replace g1 : ((5 : ℤ) ^ z1 - 2 ^ y).natAbs ∣ 3 ^ x:= by refine Int.ofNat_dvd_right.mp (by simp [g1])
    replace g2 : ((5 : ℤ) ^ z1 + 2 ^ y).natAbs ∣ 3 ^ x:= by refine Int.ofNat_dvd_right.mp (by simp [g2])
    -- Since 3 is prime, both factors must be powers of 3
    replace g1 : ∃ k1 : ℕ, k1 ≤ x ∧ ((5 : ℤ) ^ z1 - 2 ^ y).natAbs = 3 ^ k1:= (Nat.dvd_prime_pow g3).1 g1
    replace g2 : ∃ k2 : ℕ, k2 ≤ x ∧ ((5 : ℤ) ^ z1 + 2 ^ y).natAbs = 3 ^ k2:= (Nat.dvd_prime_pow g3).1 g2
    rcases g1 with ⟨k1, gk1, g1⟩
    rcases g2 with ⟨k2, gk2, g2⟩
    zify at g1 g2
    -- Show that both factors are positive
    replace g3 : (5 : ℤ) ^ z1 + 2 ^ y > 0:= by positivity
    have g4 : 3 ^ x > 0:= by positivity
    have g5 : (5 : ℤ) ^ z1 - 2 ^ y > 0:= by
      by_contra H
      simp at H
      replace H : 2 ^ y - (5 : ℤ) ^ z1 ≥ 0:= by linarith
      replace H : (2 ^ y - (5 : ℤ) ^ z1) * (5 ^ z1 + 2 ^ y) ≥ 0:= by positivity
      linarith
    -- Since both factors are positive, we can remove absolute value signs
    rw [show |(5 : ℤ) ^ z1 - 2 ^ y| = (5 : ℤ) ^ z1 - 2 ^ y by exact abs_of_pos g5] at g1
    rw [show |(5 : ℤ) ^ z1 + 2 ^ y| = (5 : ℤ) ^ z1 + 2 ^ y by exact abs_of_pos g3] at g2
    clear g3 g4 g5
    -- Since 5^z1 + 2^y > 5^z1 - 2^y, we must have k2 > k1
    have g3 : (2 : ℤ) ^ y > 0:= by positivity
    replace g3 : (5 : ℤ) ^ z1 + 2 ^ y > 5 ^ z1 - 2 ^ y:= by linarith
    rw [g1, g2] at g3
    replace g3 : k2 > k1:= by
      by_contra H
      simp at H
      replace H : 3 ^ k2 ≤ 3 ^ k1:= by refine Nat.pow_le_pow_of_le_right (by omega) H
      zify at H
      linarith
    -- Show that k1 must be 0 (i.e., 5^z1 - 2^y = 1)
    have g4 : k1 = 0:= by
      by_contra H
      replace H : k1 ≥ 1:= by omega
      have g5 : (3 : ℤ) ^ 1 ∣ 3 ^ k1:= by exact pow_dvd_pow 3 H
      have g6 : (3 : ℤ) ^ 1 ∣ 3 ^ k2:= by exact pow_dvd_pow 3 (by omega)
      simp at g5 g6
      rw [←g1] at g5
      rw [←g2] at g6
      -- This would imply 3 divides 2*5^z1, which is impossible
      replace g6 : (3 : ℤ) ∣ (5 ^ z1 - 2 ^ y) + (5 ^ z1 + 2 ^ y):= (Int.dvd_add_right g5).mpr g6
      rw [show ((5 : ℤ) ^ z1 - 2 ^ y) + (5 ^ z1 + 2 ^ y) = 2 * 5 ^ z1 by ring] at g6
      replace g6 : 3 ∣ (↑(2 * 5 ^ z1) : ℤ):= g6
      replace g6 : (3 : ℤ).natAbs ∣ 2 * 5 ^ z1:= by refine Int.ofNat_dvd_right.1 (by simp [g6])
      simp at g6
      replace g5 : Nat.Coprime 3 2:= by decide
      replace g6 : 3 ∣ 5 ^ z1:= by exact Nat.Coprime.dvd_of_dvd_mul_left g5 g6
      replace g6 : 3 ∣ 5:= by exact Nat.Prime.dvd_of_dvd_pow (by native_decide) g6
      omega
    -- Since k1 = 0, we have 5^z1 - 2^y = 1
    subst k1
    simp at g1
    rw [g1, g2] at h
    simp at h
    clear gk1 gk2 g3
    subst k2
    -- Use modular arithmetic to show that z1 must be odd and y must be even
    have g3 : 5 ≡ -1 [ZMOD 3]:= by exact rfl
    have g4 : 2 ≡ -1 [ZMOD 3]:= by exact rfl
    have g5 : 3 ≡ 0 [ZMOD 3]:= by exact rfl
    replace g3 : 5 ^ z1 ≡ (-1) ^ z1 [ZMOD 3]:= by exact Int.ModEq.pow z1 g3
    replace g4 : 2 ^ y ≡ (-1) ^ y [ZMOD 3]:= by exact Int.ModEq.pow y g4
    replace g5 : 3 ^ x ≡ 0 ^ x [ZMOD 3]:= by exact Int.ModEq.pow x g5
    rw [show (0 : ℤ) ^ x = 0 by exact Mathlib.Tactic.Ring.zero_pow hx] at g5
    rw [←g2] at g5
    have g6 : 5 ^ z1 + 2 ^ y ≡ (-1) ^ z1 + (-1) ^ y [ZMOD 3]:= by exact Int.ModEq.add g3 g4
    replace g6 : (-1) ^ z1 + (-1) ^ y ≡ 0 [ZMOD 3]:= Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm g5)) g6)
    replace g5 : 5 ^ z1 - 2 ^ y ≡ (-1) ^ z1 - (-1) ^ y [ZMOD 3]:= by exact Int.ModEq.sub g3 g4
    rw [g1] at g5
    replace g5 : (-1) ^ z1 - (-1) ^ y ≡ 1 [ZMOD 3]:= by exact id (Int.ModEq.symm g5)
    -- Add and subtract the equations to get constraints on z1 and y
    have g7 : (-1) ^ z1 + (-1) ^ y + ((-1) ^ z1 - (-1) ^ y) ≡ 0 + 1 [ZMOD 3]:= Int.ModEq.add g6 g5
    rw [show (-1) ^ z1 + (-1) ^ y + ((-1) ^ z1 - (-1) ^ y) = 2 * (-1) ^ z1 by ring] at g7
    simp at g7
    have g8 : (-1) ^ z1 + (-1) ^ y - ((-1) ^ z1 - (-1) ^ y) ≡ 0 - 1 [ZMOD 3]:= Int.ModEq.sub g6 g5
    rw [show (-1) ^ z1 + (-1) ^ y - ((-1) ^ z1 - (-1) ^ y) = 2 * (-1) ^ y by ring] at g8
    simp at g8
    -- From these equations, we can conclude that z1 must be odd
    have h2 : Odd z1:= by
      by_contra H
      simp at H
      replace H : (-1) ^ z1 = 1:= by exact Even.neg_one_pow H
      rw [H] at g7
      simp at g7
      replace g7 : (3 : ℤ) ∣ (2 - 1):= by exact Int.dvd_sub_of_emod_eq g7
      omega
    -- And y must be even
    have h3 : Even y:= by
      by_contra H
      simp at H
      replace H : (-1) ^ y = -1:= by exact Odd.neg_one_pow H
      rw [H] at g8
      simp at g8
      replace g8 : (3 : ℤ) ∣ (2 - 1):= by exact Int.dvd_sub_of_emod_eq g8
      omega
    clear g3 g4 g5 g6 g7 g8
    -- Since y is even and positive, y ≥ 2
    have h4 : y ≥ 2:= by
      by_contra H
      simp at H
      replace H : y = 1:= by omega
      rw [H] at h3
      have _ : Odd 1:= by decide
      trivial
    -- Show that x must also be even
    have h5 : Even x:= by
      rw [show y = 2 + (y - 2) by omega] at g2
      rw [show (2 : ℤ) ^ (2 + (y - 2)) = 2 ^ 2 * 2 ^ (y - 2) by ring] at g2
      rw [show (2 : ℤ) ^ 2 = 4 by omega] at g2
      -- Use modular arithmetic modulo 4
      have g1 : 4 ≡ 0 [ZMOD 4]:= by exact rfl
      replace g1 : 4 * 2 ^ (y - 2) ≡ 0 * 2 ^ (y - 2) [ZMOD 4]:= by exact Int.ModEq.mul g1 rfl
      simp at g1
      have g3 : 5 ≡ 1 [ZMOD 4]:= by exact rfl
      have g4 : 3 ≡ -1 [ZMOD 4]:= by exact rfl
      replace g4 : 3 ^ x ≡ (-1) ^ x [ZMOD 4]:= by exact Int.ModEq.pow x g4
      replace g3 : 5 ^ z1 ≡ 1 ^ z1 [ZMOD 4]:= by exact Int.ModEq.pow z1 g3
      simp at g3
      rw [←g2] at g4
      replace g3 : 5 ^ z1 + 4 * 2 ^ (y - 2) ≡ 1 + 0 [ZMOD 4]:= Int.ModEq.symm (Int.ModEq.add (id (Int.ModEq.symm g3)) (id (Int.ModEq.symm g1)))
      simp at g3
      replace g3 : 1 ≡ (-1) ^ x [ZMOD 4]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g3)) g4
      -- This shows x must be even
      by_contra H
      simp at H
      replace H : (-1) ^ x = -1:= by exact Odd.neg_one_pow H
      rw [H] at g3
      replace g3 : (4 : ℤ) ∣ (1 - (-1)):= by exact Int.ModEq.dvd (id (Int.ModEq.symm g3))
      omega
    -- Since x is even, we can write x = 2*x1
    replace h5 : 2 ∣ x:= by exact even_iff_two_dvd.mp h5
    replace h5 : ∃ k : ℕ, x = 2 * k:= by exact h5
    rcases h5 with ⟨x1, h5⟩
    -- Since z1 is odd, we can write z1 = 2*z2 + 1
    replace h3 : ∃ k : ℕ, z1 = 2 * k + 1:= by exact h2
    rcases h3 with ⟨z2, h3⟩
    rw [h3, h5] at g2
    -- Rewrite the equation using the new variables
    rw [show (5 : ℤ) ^ (2 * z2 + 1) = (5 ^ (2 * z2)) * 5 by ring] at g2
    rw [show (3 : ℤ) ^ (2 * x1) = (3 ^ 2) ^ x1 by exact pow_mul 3 2 x1] at g2
    rw [show (5 : ℤ) ^ (2 * z2) = (5 ^ 2) ^ z2 by exact pow_mul 5 2 z2] at g2
    rw [show (3 : ℤ) ^ 2 = 9 by omega] at g2
    rw [show (5 : ℤ) ^ 2 = 25 by omega] at g2
    -- Show that y must be exactly 2
    have h6 : y = 2:= by
      by_contra H
      replace H : y ≥ 3:= by omega
      rw [show y = 3 + (y - 3) by omega] at g2
      rw [show (2 : ℤ) ^ (3 + (y - 3)) = 2 ^ 3 * 2 ^ (y - 3) by ring] at g2
      rw [show (2 : ℤ) ^ 3 = 8 by omega] at g2
      -- Use modular arithmetic modulo 8 to show this is impossible
      have g1 : 8 ≡ 0 [ZMOD 8]:= by exact rfl
      have g3 : 25 ≡ 1 [ZMOD 8]:= by exact rfl
      have g4 : 9 ≡ 1 [ZMOD 8]:= by exact rfl
      replace g1 : 8 * 2 ^ (y - 3) ≡ 0 * 2 ^ (y - 3) [ZMOD 8]:= by exact Int.ModEq.mul g1 rfl
      simp at g1
      replace g3 : (25 : ℤ) ^ z2 ≡ 1 ^ z2 [ZMOD 8]:= by exact Int.ModEq.pow z2 g3
      replace g4 : (9 : ℤ) ^ x1 ≡ 1 ^ x1 [ZMOD 8]:= by exact Int.ModEq.pow x1 g4
      simp at g3 g4
      replace g3 : (25 : ℤ) ^ z2 * 5 ≡ 1 * 5 [ZMOD 8]:= by exact Int.ModEq.mul g3 rfl
      simp  at g3
      replace g3 : 25 ^ z2 * 5 + 8 * 2 ^ (y - 3) ≡ 5 + 0 [ZMOD 8]:= by exact Int.ModEq.add g3 g1
      rw [g2] at g3
      simp at g3
      replace g3 : 5 ≡ 1 [ZMOD 8]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g3)) g4
      replace g3 : (8 : ℤ) ∣ (5 - 1):= by exact Int.dvd_sub_of_emod_eq g3
      omega
    -- Since y = 2, we can solve for z1
    subst y
    simp at g1
    replace g1 : (5 : ℤ) ^ z1 = 5 ^ 1:= by linarith only [g1]
    simp at g1
    replace g1 : z1 = 1:= by
      by_contra H
      replace H : z1 ≥ 2:= by omega
      replace H : 5 ^ z1 ≥ 5 ^ 2:= by refine Nat.pow_le_pow_of_le_right (by omega) H
      zify at H
      linarith
    -- Since z1 = 1, we have z2 = 0
    subst z1
    replace g1 : z2 = 0:= by linarith
    subst z2
    simp at g2
    -- Finally, solve for x1
    replace g2 : x1 = 1:= by
      by_contra H
      replace H : x1 ≥ 2:= by omega
      replace H : 9 ^ x1 ≥ 9 ^ 2:= by refine Nat.pow_le_pow_of_le_right (by omega) H
      zify at H
      linarith
    -- This gives us x = 2, y = 2, z = 2
    subst x1
    simp at h1 h5
    simp [h1, h5]
  .
    -- Reverse direction: if x = y = z = 2, then 3^x + 4^y = 5^z
    intro h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp
