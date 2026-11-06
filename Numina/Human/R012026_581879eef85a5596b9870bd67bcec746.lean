import Mathlib

/- These are the Int version of Nat.gcd_eq -/
lemma gcd_eq (h : a ≡ b [ZMOD m]) : gcd a m = gcd b m := by
  have h1 := gcd_dvd_right a m
  have h2 := gcd_dvd_right b m
  apply Int.dvd_antisymm
  exact Int.le.intro_sub (a.gcd m + 0) rfl
  exact Int.le.intro_sub (b.gcd m + 0) rfl
  apply dvd_gcd
  · have := Int.ModEq.dvd h
    have h3 : gcd a m ∣ b - a := by trans m; exact h1; exact this
    have h4 : gcd a m ∣ a := by exact gcd_dvd_left a m
    exact (Int.dvd_iff_dvd_of_dvd_sub h3).mpr h4
  · exact h1
  apply dvd_gcd
  · have := Int.ModEq.dvd h.symm
    have h5 : gcd b m ∣ a - b := by trans m; exact h2; exact this
    have h6 : gcd b m ∣ b := by exact gcd_dvd_left b m
    exact(Int.dvd_iff_dvd_of_dvd_sub h5).mpr h6
  · exact h2

lemma gcd_eq' (h : a ≡ b [ZMOD m]) : a.gcd m = b.gcd m := by
  have h1 : a.gcd m = gcd a m := by exact rfl
  have h2 : b.gcd m = gcd b m := by exact rfl
  have : (a.gcd m : ℤ) = b.gcd m := by
    rw [h1, gcd_eq h, h2]
  norm_cast at this

/-4. Let $p$ be a prime of the form $4k+3$. Prove that if $p \mid a^{2}+b^{2}$, then $p \mid a$ and $p \mid b$, where $a, b \in \mathbf{Z}$.-/
theorem number_theory_187348 (p : ℕ) (a b : ℤ) (hp : Prime p)
  (hpk : ∃ k : ℕ, p = 4 * k + 3) (hab : ↑p ∣ a ^ 2 + b ^ 2) :
    ↑p ∣ a ∧ ↑p ∣ b := by

    /-利用反证法-/
    by_contra h
    apply not_and_or.mp at h

    -- 不妨假设 ¬ p ∣ a
    wlog hpa : ¬ (p : ℤ) ∣ a
    · push_neg at hpa
      apply not_and_or.mpr at h
      apply not_and.mp at h
      have hpb := h hpa
      apply this p b a hp hpk
      rwa [add_comm]
      exact Or.inl hpb
      exact hpb

    have : Fact (Nat.Prime p) := by refine { out := ?_ }; exact Prime.nat_prime hp

    -- 有 ¬ p ∣ b
    have hpb : ¬ (p : ℤ) ∣ b := by
      intro h_dvd_b
      have h1 : (p : ℤ) ∣ b ^ 2 := by
        apply dvd_pow
        assumption
        norm_num

      -- 否则若 p ∣ b, 则 p ∣ a^2 + b^2 - b^2 = a^2 → p ∣ a
      have h2 : (p : ℤ) ∣ (a ^ 2 + b ^ 2) - b ^ 2 := by exact Int.dvd_sub hab h1
      simp at h2

      have : (p : ℤ) ∣ a := by
        apply Int.Prime.dvd_pow' (k := 2)
        exact Prime.nat_prime hp
        exact h2

      contradiction

    -- 因此 b 与 p 互素
    have h_coprime_b_p : IsCoprime b p := by
      have : Irreducible (p : ℤ) := by
        refine irreducible_iff_prime.mpr ?_
        refine Nat.prime_iff_prime_int.mp ?_
        exact Prime.nat_prime hp
      apply IsCoprime.symm
      exact (Irreducible.coprime_iff_not_dvd this).mpr hpb

    let a' := (a : ZMod p)
    let b' := (b : ZMod p)

    -- b 使得 a^2 = -b^2 (mod p)
    have h_a'_b'_sq : a' ^ 2 = -b' ^ 2 := by
      unfold a' b'
      rw [← Int.cast_pow, ← Int.cast_pow, ← Int.cast_neg]
      apply ZMod.intCast_eq_intCast_iff _ _ p |>.mpr
      symm
      apply Int.modEq_iff_dvd.mpr
      simp only [sub_neg_eq_add, hab]

    -- 由于 b 与 p 互素，存在 b 模 p 的逆元，故 -1 为模 p 的二次剩余
    have : (a' * b'⁻¹) ^ 2 = -1 := by
      rw [mul_pow, h_a'_b'_sq, neg_mul, ← mul_pow]
      congr 1
      have : b' * b'⁻¹ = 1 := by
        rw [ZMod.mul_inv_eq_gcd]
        simp [b']

        have : b'.val.gcd p = b.gcd p := by
          have : b'.val.gcd p = (b'.val : ℤ).gcd p := by norm_cast
          rw [this]
          unfold b'
          rw [ZMod.val_intCast]

          apply gcd_eq'
          unfold Int.ModEq
          simp only [dvd_refl, Int.emod_emod_of_dvd]
        rw [this]

        have : b.gcd p = 1 := by exact Int.isCoprime_iff_gcd_eq_one.mp h_coprime_b_p
        rw [this]
        norm_num

      rw [this]
      simp only [one_pow]

    have : IsSquare (-1 : ZMod p) := by
      use a' * b'⁻¹
      rw [← this]
      ring

    -- -1 为模 p 的二次剩余 ↔ p = 4k+1，矛盾
    have : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp this
    have : p % 4 = 3 := by
      obtain ⟨k, hk⟩ := hpk
      rw [hk, show 3 = 3 % 4 by norm_num]
      exact Nat.mul_add_mod 4 k (3 % 4)

    contradiction
