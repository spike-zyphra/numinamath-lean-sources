import Mathlib

/- Let $n \geq 3$ be an integer such that $4 n+1$ is a prime number. Prove that $4 n+1$ divides $n^{2 n}-1$. -/
theorem number_theory_238432 (n : ℕ) (hn : 3 ≤ n) (hprime : Nat.Prime (4 * n + 1)) : (4 * n + 1) ∣ n^(2 * n) - 1 := by
  -- Rewrite the goal in terms of modulo.
  rw [<-Nat.modEq_iff_dvd']
  -- Note that -4n ≡ 1 (mod 4n + 1).
  have h₁ : -4 * n ≡ 1 [ZMOD (4 * n + 1 : ℕ)] := by
    rw [Int.modEq_iff_dvd]
    simp
    rw [add_comm]
  -- Let x be the multiplicative inverse of 2 modulo 4n + 1.
  let x := (-4 : ZMod (4 * n + 1))⁻¹
  -- Show that (-4) * n ≡ 1 (mod p).
  have h₂ : (n : ZMod (4 * n + 1)) * 2 ^ 2 = -1 := by
    norm_cast
    rw [show ((n * 2 ^ 2 : ℕ) : ZMod (4 * n + 1)) = ((n * 2 ^ 2 : ℤ) : ZMod (4 * n + 1)) by norm_cast]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    zify
    rw [Int.negSucc_eq]
    ring_nf
    rw [<-neg_sub, sub_neg_eq_add, add_comm]
    rw [Int.dvd_neg]
  replace h₂ : (-4) * (n : ZMod (4 * n + 1)) = 1 := by
    ring_nf at h₂ ⊢
    rw [h₂]
    simp
  -- We have n = x.
  replace h₂ : n = x := by
    apply ZMod.inv_eq_of_mul_eq_one at h₂
    simp [x]
    exact h₂.symm
  rw [<-ZMod.eq_iff_modEq_nat]
  -- Let y = (2 : ZMod (4 * n + 1))⁻¹.
  let y := (2 : ZMod (4 * n + 1))⁻¹
  -- Show that x = -y².
  have h₃ : x = -y ^ 2 := by
    simp [x, y]
    apply ZMod.inv_eq_of_mul_eq_one
    ring_nf
    suffices (2⁻¹ * 2 : ZMod (4 * n + 1)) = 1 by
      replace this := congr_arg (· ^ 2) this
      simp only at this
      rw [mul_pow] at this
      norm_num at this
      exact this
    -- Verify that 2 is a unit, so 2⁻¹ * 2 = 1.
    rw [ZMod.inv_mul_eq_one_of_isUnit]
    rw [show (2 : ZMod (4 * n + 1)) = (2 : ℕ) by norm_cast]
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    -- We have 4n + 1 ∤ 2.
    by_contra!
    apply Nat.le_of_dvd at this
    omega
    norm_num
  suffices 1 = x ^ (2 * n) by
    rw [<-h₂] at this
    simp [this]
  -- It suffices to show that x ^ (2n) = 1 in Z/(4n + 1)Z.
  rw [h₃, pow_mul, neg_sq, <-pow_mul, <-pow_mul]
  rw [show 2 * (2 * n) = (4 * n + 1) - 1 by omega]
  symm
  -- Apply Fermat's little theorem (y ≠ 0).
  apply @ZMod.pow_card_sub_one_eq_one (4 * n + 1) (fact_iff.mpr hprime)
  -- Verify that y ≠ 0.
  by_contra!
  have h₄ : y * (2 : ZMod (4 * n + 1)) = (1 : ZMod (4 * n + 1)) := by
    simp only [y]
    -- Verify that 2 is a unit, so 2⁻¹ * 2 = 1.
    rw [ZMod.inv_mul_eq_one_of_isUnit]
    rw [show (2 : ZMod (4 * n + 1)) = (2 : ℕ) by norm_cast]
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    -- We have 4n + 1 ∤ 2.
    by_contra!
    apply Nat.le_of_dvd at this
    omega
    norm_num
  simp [this] at h₄
  rw [show (0 : ZMod (4 * n + 1)) = (0 : ℕ) by norm_cast, show (1 : ZMod (4 * n + 1)) = (1 : ℕ) by norm_cast, ZMod.eq_iff_modEq_nat, Nat.modEq_iff_dvd'] at h₄
  simp at h₄
  norm_num [h₄] at hprime
  norm_num
  -- Verify that 1 ≤ n ^ (2n), which is implicitly used in the above proof.
  rw [show 1 = n ^ 0 by simp]
  apply Nat.pow_le_pow_of_le_right
  omega
  omega
