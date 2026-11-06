import Mathlib
/- Let $E$ be an even natural number such that $E = 2p$ for some prime number $p > 3$. Let $n = \frac{2^E-1}{3}$. Prove that $n$ divides $2^n-2$. -/
theorem number_theory_637454 (p n : ℕ) (hn : n = (2 ^ (2 * p) - 1) / 3) (hp : Nat.Prime p) (hp1 : Odd p) (hp2 : p > 3) : n ∣ 2 ^ n - 2:= by
  -- First, we establish that 3 divides 2^(2p) - 1, so n is indeed an integer
  replace hn : 3 * n = 2 ^ (2 * p) - 1:= by
    -- We need to show that 3 divides 2^(2p) - 1
    suffices 3 ∣ 2 ^ (2 * p) - 1 by rw [hn] ; omega
    zify
    field_simp
    -- This is equivalent to showing 2^(2p) ≡ 1 (mod 3)
    suffices 2 ^ (2 * p) ≡ 1 [ZMOD 3] by exact Int.dvd_sub_of_emod_eq this
    -- Since 2 ≡ -1 (mod 3), we have 2^(2p) ≡ (-1)^(2p) ≡ 1 (mod 3)
    have g : 2 ≡ -1 [ZMOD 3]:= by rfl
    replace g:= Int.ModEq.pow (2 * p) g
    simp at g
    exact g
  -- Show that n ≥ 1 (n is positive)
  have g : n ≥ 1:= by
    by_contra H
    simp at H
    subst n
    simp at hn
    have g1 : 2 ^ (2 * p) ≥ 2 ^ 1:= by
      have g1 : 2 * p ≥ 1:= by omega
      refine Nat.pow_le_pow_of_le_right (by omega) g1
    omega
  -- Consequently, 2^n ≥ 2
  replace g : 2 ^ n ≥ 2 ^ 1:= by refine Nat.pow_le_pow_of_le_right (by omega) g
  simp at g
  -- Define A = 2^p - 1 and B = (2^p + 1)/3
  set A:= 2 ^ p - 1 with hA
  set B:= (2 ^ p + 1) / 3 with hB
  clear_value A B
  -- Show that 3 divides 2^p + 1
  have h1 : 3 ∣ 2 ^ p + 1:= by
    zify
    suffices 2 ^ p + 1 ≡ 0 [ZMOD 3] by exact Int.dvd_of_emod_eq_zero this
    have g : 2 ≡ -1 [ZMOD 3]:= by rfl
    replace g := Int.ModEq.pow p g
    -- Since p is odd, (-1)^p = -1
    rw [show (-1) ^ p = -1 by exact Odd.neg_one_pow hp1] at g
    replace g : 2 ^ p + 1 ≡ -1 + 1 [ZMOD 3]:= by exact Int.ModEq.add g rfl
    simp at g
    exact g
  -- Show that A and B are coprime
  have h2 : Nat.Coprime A B:= by
    have h2 : 2 ^ p ≥ 2 ^ 4:= by refine Nat.pow_le_pow_of_le_right (by omega) (by omega)
    have h3 : 3 * B = 2 ^ p + 1:= by rw [hB] ; omega
    rw [show 2 ^ p + 1 = A + 2 by rw [hA] ; omega] at h3
    suffices Nat.Coprime A (3 * B) by exact Nat.Coprime.coprime_mul_left_right this
    rw [h3]
    rw [show A + 2 = 1 * A + 2 by simp]
    suffices Nat.Coprime A 2 by exact (Nat.coprime_mul_right_add_right A 2 1).mpr this
    -- A is odd, so it's coprime with 2
    suffices Odd A by exact Nat.coprime_two_right.mpr this
    by_contra H
    simp at H
    replace H : Odd (A + 1):= by exact Even.add_one H
    subst A
    rw [show 2 ^ p - 1 + 1 = 2 ^ p by omega] at H
    absurd H
    simp
    suffices Even 2 by refine (Nat.even_pow' (by omega)).mpr this
    decide
  -- Show that n = A * B
  have h3 : n = A * B:= by
    suffices 3 * n = A * (3 * B) by linarith
    rw [show 3 * B = 2 ^ p + 1 by subst B ; omega]
    suffices 3 * n + 2 ^ p + 1 = (A + 1) * (2 ^ p + 1) by linarith
    have g1 : 2 ^ (2 * p) > 0:= by positivity
    have g2 : 2 ^ p > 0:= by positivity
    rw [show 3 * n + 2 ^ p + 1 = 2 ^ (2 * p) + 2 ^ p by rw [hn] ; omega]
    rw [show A + 1 = 2 ^ p by rw [hA] ; omega]
    ring_nf
  -- Show that p and 3 are coprime
  have g3 : Nat.Coprime p 3:= by
    have g3 : Nat.Prime 3:= by norm_num
    replace hp2 : p ≠ 3:= by omega
    exact (Nat.coprime_primes hp g3).mpr hp2
  -- Main goal: show 2^n ≡ 2 (mod A*B), which implies n | (2^n - 2)
  suffices 2 ^ n ≡ 2 [MOD A * B] by rw [←h3] at this ; exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm this))
  -- Show 2^n ≡ 2 (mod A)
  have h4 : 2 ^ n ≡ 2 [MOD A]:= by
    have h4 : Nat.Coprime 2 p:= by exact Nat.coprime_two_left.mpr hp1
    replace h4:= Nat.ModEq.pow_totient h4
    rw [show p.totient = p - 1 by exact Nat.totient_prime hp] at h4
    replace h4 : 2 * 2 ^ (p - 1) ≡ 2 * 1 [MOD p]:= by exact Nat.ModEq.mul rfl h4
    rw [show 2 * 2 ^ (p - 1) = 2 ^ (1 + (p - 1)) by ring] at h4
    rw [show 1 + (p - 1) = p by omega] at h4
    simp at h4
    replace h4:= Nat.ModEq.mul h4 h4
    ring_nf at h4
    rw [show p * 2 = 2 * p by ring] at h4
    rw [show 4 = 3 + 1 by omega] at h4
    have g1 : 2 ^ (2 * p) > 0:= by positivity
    rw [show 2 ^ (2 * p) = 3 * n + 1 by rw [hn] ; omega] at h4
    replace h4 : 3 * n ≡ 3 [MOD p]:= by exact Nat.ModEq.add_right_cancel' 1 h4
    have g2 : n ≥ 1:= by
      by_contra H
      simp at H
      rw [H] at g
      simp at g
    replace h4 : p ∣ 3 * n - 3:= by exact (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h4))
    rw [show 3 * n - 3 = 3 * (n - 1) by omega] at h4
    replace h4 : p ∣ n - 1:= by exact Nat.Coprime.dvd_of_dvd_mul_left g3 h4
    rcases h4 with ⟨k, hk⟩
    replace hk : n = p * k + 1:= by omega
    have g4 : 2 ^ p ≡ 1 [MOD A]:= by
      suffices 1 ≡ 2 ^ p [MOD A] by exact id (Nat.ModEq.symm this)
      replace g1 : 2 ^ p > 0:= by positivity
      replace g1 : 2 ^ p ≥ 1:= by omega
      suffices A ∣ 2 ^ p - 1 by exact (Nat.modEq_iff_dvd' g1).mpr this
      rw [hA]
    replace g4:= Nat.ModEq.pow k g4
    ring_nf at g4
    replace g4 : 2 ^ (p * k) * 2 ≡ 1 * 2 [MOD A]:= by exact Nat.ModEq.mul g4 rfl
    rw [show 2 ^ (p * k) * 2 = 2 ^ (p * k + 1) by ring] at g4
    simp at g4
    rw [hk]
    exact g4
  -- Show 2^n ≡ 2 (mod B)
  have h5 : 2 ^ n ≡ 2 [MOD B]:= by
    have h5 : n ≡ 1 [MOD 2 * p]:= by
      have g1 : n ≥ 1:= by
        by_contra H
        simp at H
        rw [H] at g
        simp at g
      suffices 2 * p ∣ n - 1 by exact Nat.ModEq.symm ((Nat.modEq_iff_dvd' g1).mpr this)
      have g2 : Nat.Coprime 2 3:= by norm_num
      replace g2 : Nat.Coprime (2 * p) 3:= by exact Nat.Coprime.mul g2 g3
      suffices 2 * p ∣ 3 * (n - 1) by exact Nat.Coprime.dvd_of_dvd_mul_left g2 this
      -- Show that 2 divides 3*(n-1)
      have h5 : 2 ∣ 3 * (n - 1):= by
        suffices Even (3 * (n - 1)) by exact even_iff_two_dvd.mp this
        by_contra H
        simp at H
        have H1 : Odd 3:= by decide
        replace H : Even (3 * (n - 1) + 3):= by exact Odd.add_odd H H1
        rw [show 3 * (n - 1) + 3 = 3 * n by omega] at H
        replace H : Odd (3 * n + 1):= by exact Even.add_one H
        replace hn : 3 * n + 1 = 2 ^ (2 * p):= by omega
        rw [hn] at H
        absurd H
        simp
        suffices Even 2 by refine (Nat.even_pow' (by omega)).mpr this
        decide
      replace g2 : Nat.Coprime 2 p:= by exact Nat.coprime_two_left.mpr hp1
      suffices p ∣ 3 * (n - 1) by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd g2 h5 this
      replace h4:= Nat.ModEq.pow_totient g2
      rw [show p.totient = p - 1 by exact Nat.totient_prime hp] at h4
      replace h4 : 2 * 2 ^ (p - 1) ≡ 2 * 1 [MOD p]:= by exact Nat.ModEq.mul rfl h4
      rw [show 2 * 2 ^ (p - 1) = 2 ^ (1 + (p - 1)) by ring] at h4
      rw [show 1 + (p - 1) = p by omega] at h4
      simp at h4
      replace h4:= Nat.ModEq.mul h4 h4
      ring_nf at h4
      rw [show p * 2 = 2 * p by ring] at h4
      replace g3 : 2 ^ (2 * p) > 0:= by positivity
      rw [show 2 ^ (2 * p) = 3 * n + 1 by rw [hn] ; omega] at h4
      rw [show 4 = 3 + 1 by omega] at h4
      replace h4 : 3 * n ≡ 3 [MOD p]:= by exact Nat.ModEq.add_right_cancel' 1 h4
      replace h4 : p ∣ 3 * n - 3:= by refine (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h4))
      rw [show 3 * n - 3 = 3 * (n - 1) by omega] at h4
      exact h4
    replace g3 : n ≥ 1:= by
      by_contra H
      simp at H
      rw [H] at g
      simp at g
    replace h5 : 2 * p ∣ n - 1:= by exact (Nat.modEq_iff_dvd' g3).mp (id (Nat.ModEq.symm h5))
    rcases h5 with ⟨k, hk⟩
    replace hk : n = 2 * p * k + 1:= by omega
    replace h3 : B ∣ 3 * n:= by use 3 * A ; linarith
    rw [hn] at h3
    have g2 : 2 ^ (2 * p) > 0:= by positivity
    replace g2 : 2 ^ (2 * p) ≥ 1:= by omega
    replace h3 : 1 ≡ 2 ^ (2 * p) [MOD B]:= by exact (Nat.modEq_iff_dvd' g2).mpr h3
    replace h3:= Nat.ModEq.pow k h3
    ring_nf at h3
    replace h3 : 2 * 1 ≡ 2 * 2 ^ (k * p * 2) [MOD B]:= by exact Nat.ModEq.mul rfl h3
    rw [show 2 * 2 ^ (k * p * 2) = 2 ^ n by rw [hk] ; ring] at h3
    simp at h3
    exact id (Nat.ModEq.symm h3)
  -- Use Chinese Remainder Theorem to combine the two congruences
  refine (Nat.modEq_and_modEq_iff_modEq_mul h2).mp ⟨h4, h5⟩
