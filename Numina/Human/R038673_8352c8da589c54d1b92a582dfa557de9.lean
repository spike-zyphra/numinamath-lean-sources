import Mathlib

/- What is the average of the two smallest positive integer solutions
 to the congruence $$14u \equiv 46 \pmod{100}~?$$ -/
theorem number_theory_23102 (u1 u2 : ℕ) (u1pos : u1 > 0) (u2pos : u2 > 0)
    (u1ltu2 : u1 < u2) (modeq_u1 : 14 * u1 ≡ 46 [MOD 100])
    (modeq_u2 : 14 * u2 ≡ 46 [MOD 100])
    (two_smallest: ∀u:ℕ, 14 * u ≡ 46 [MOD 100] → u ≠ u1 → u ≥ u2) :
    (u1 + u2) / 2 = 64 := by
  -- to solve the equation, we should simplify equation 14u ≡ 46 (mod 100)
  -- first, we prove it is equivalent to u ≡ -11 (mod 50)
  have modeq_iff(u: ℕ): 14*u ≡ 46 [MOD 100] ↔ u ≡ -11 [ZMOD 50] := by
    -- note that 14, 46, 100 all have a factor of 2, so we can divide it out.
    -- then it reduces to 7u ≡ 23 (mod 50)
    have h1: 14*u ≡ 46 [MOD 100] ↔ 7*u ≡ 23 [MOD 50] := by
      have: 2 ≠ 0 := by norm_num
      constructor <;> intro h
      · apply (Nat.ModEq.mul_left_cancel_iff' this).mp
        simp [← mul_assoc, h]
      · replace := (Nat.ModEq.mul_left_cancel_iff' this).mpr h
        simp [← mul_assoc] at this; exact this
    -- next, multiply both sides by 7 to obtain 49u ≡ 161 (mod 50)
    have h2: 7*u ≡ 23 [MOD 50] ↔ 49*u ≡ 161 [MOD 50] := by
      constructor <;> intro h
      · have: 7 ≡ 7 [MOD 50] := rfl
        replace := Nat.ModEq.mul h this
        simp [mul_comm 7 u, mul_assoc] at this
        simp [mul_comm 49 u, this]
      · -- 7 and 50 are coprime, so inverse exist. in fact, it is 43
        -- so multiply both sides by 7⁻¹(=43).
        have hh1: 43 ≡ 43 [MOD 50] := rfl
        have hh2: 161 * 43 ≡ 23 [MOD 50] := rfl
        have := Nat.ModEq.mul h hh1
        apply Nat.ModEq.trans (Nat.ModEq.trans ?_ this) hh2
        -- 7u modeq 7u (7 x 7⁻¹) modeq 49u x 7⁻¹
        replace: 49*u*43 = 7*u * (7*43) := by ring
        rw [← mul_one (7*u), this]
        apply Nat.ModEq.mul rfl (by exact rfl)
    -- finally, replace 49u ≡ 161 (mod 50) both sides by a (mod 50) equivalent term
    -- and it turns out to be -u ≡ 11, or u ≡ -11
    have h3: 49*u ≡ 161 [MOD 50] ↔ u ≡ -11 [ZMOD 50] := by
      have: 49*u ≡ -u [ZMOD 50] := by
        have: 49*(u:ℤ) = -u + 50*u := by ring
        rw [this]
        exact Int.modEq_add_fac_self
      rw [← Int.natCast_modEq_iff]
      push_cast; constructor <;> intro h
      · apply Int.neg_modEq_neg.mp
        apply Int.ModEq.trans this.symm
        apply Int.ModEq.trans rfl h
      · apply Int.ModEq.trans this
        apply Int.neg_modEq_neg.mp
        apply Int.ModEq.trans (by simp) h
    -- so given congruence equation is equivalent to u ≡ -11 (mod 50)
    rw [h1, h2, h3]
  -- for equation u ≡ -11 (mod 50), u must have the form of u = 50t - 11
  have eq_of_modeq(u: ℕ)(hu: u ≡ -11 [ZMOD 50]):
    ∃(t:ℤ), (u = -11 + t*50 ∧ 0 < t) := by
    rcases (Int.modEq_iff_add_fac.mp hu.symm) with ⟨t, ht⟩
    use t; simp [ht, mul_comm]
    have := Int.ofNat_zero_le u
    rw [ht] at this; linarith [this]
  -- smallest positive integer satisfy u ≡ -11 (mod 50) is 39
  have hu1(u:ℕ)(hu: u ≡ -11 [ZMOD 50]): u ≥ 39 := by
    rcases (eq_of_modeq u hu) with ⟨t, ht, tpos⟩
    rw [← Order.one_le_iff_pos] at tpos
    zify; simp [ht, tpos]
  -- then u1 = 39
  have u1eq: u1 = 39 := by
    by_contra!
    replace := two_smallest 39
      (by rw [modeq_iff]; exact rfl) this.symm
    have u2leu1: u2 ≤ u1 := by
      apply le_trans this
      apply hu1 u1
      rw [← modeq_iff u1]; exact modeq_u1
    linarith [u1ltu2, u2leu1]
  -- the second smallest satisfy equation is 89
  have hu2(u:ℕ)(hu: u ≡ -11 [ZMOD 50])(uneu1: u ≠ u1):
    u ≥ 89 := by
    rcases (eq_of_modeq u hu) with ⟨t, ht, tpos⟩
    have tge2: 2 ≤ t := by
      have: 1 < t := by
        apply lt_of_le_of_ne (by exact tpos)
        by_contra!; zify at uneu1
        simp [ht, this.symm, u1eq] at uneu1
      exact this
    zify; rw [ht]
    linarith [tge2]
  -- therefore u2 = 89
  have u2eq: u2 = 89 := by
    apply le_antisymm ?_ ?_
    · apply two_smallest 89 ?_ (by simp [u1eq])
      rw [modeq_iff 89]; rfl
    · apply hu2 u2 ?_ u1ltu2.ne'
      simp only [← modeq_iff u2, modeq_u2]
  -- u1=39, u2=89, so their average is 64. done.
  simp [u1eq, u2eq]