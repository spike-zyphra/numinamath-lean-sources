import Mathlib

/- Trouver les triplets d'entiers $(x, y, n)$ tels que $n^{2}=17 x^{4}-32 x^{2} y^{2}+41 y^{4}$. -/
theorem algebra_607426 (x y n : ℤ) :
  n^2 = 17 * x^4 - 32 * x^2 * y^2 + 41 * y^4 ↔ (x, y, n) = (0, 0, 0) := by

  -- a^2 mod 3 is 1 or 0
  have sq_mod3 (a:ℤ): a^2 ≡ 0 [ZMOD 3] ∨ a^2 ≡ 1 [ZMOD 3] := by
    mod_cases h: a % 3
    · left
      have: (0:ℤ) = 0^2 := by simp
      rw [this]
      exact Int.ModEq.pow 2 h
    · right
      have: (1:ℤ) = 1^2 := by simp
      rw [this]
      exact Int.ModEq.pow 2 h
    · replace h: a ≡ -1 [ZMOD 3] := by exact h
      right
      have: (1:ℤ) = (-1)^2 := by simp
      rw [this]
      exact Int.ModEq.pow 2 h

  -- if a^2 mod 3 = -b^2, then must be the case both mod 3 is 0.
  have dvd_of_sq_mod3 {a b: ℤ} (h: a^2 ≡ -b^2 [ZMOD 3]):
    3 ∣ a ∧ 3 ∣ b := by
    have p3: Prime (3:ℤ) := Int.prime_three
    rcases (sq_mod3 a) with ha0 | ha1
    · rcases (sq_mod3 b) with hb0 | hb1
      · constructor
        all_goals
          exact Prime.dvd_of_dvd_pow Int.prime_three
            (Int.dvd_of_emod_eq_zero (by assumption))
      · have: 0 ≡ -1 [ZMOD 3] := by
          apply ha0.symm.trans (h.trans ?_)
          exact Int.neg_modEq_neg.mpr hb1
        contradiction
    · rcases (sq_mod3 b) with hb | hb
      all_goals
        have := ha1.symm.trans (h.trans
          (Int.neg_modEq_neg.mpr hb))
        contradiction

  -- if (9a,3b,3c) is a solution, then (a,b,c) also a solution.
  have hnxy {a b c: ℤ}  (h: (9*a)^2 = 17*(3*b)^4 -
    32*(3*b)^2 * (3*c)^2 + 41 * (3*c)^4):
    a^2 = 17 * b^4 - 32 * b^2 * c^2 + 41 * c^4 := by
    have: (9*a)^2 = 81 * a^2 := by ring
    rw [this] at h
    linarith only [h]

  -- na + b mod n is b
  have modeq_add_fac {a b: ℤ}: 3*a + b ≡ b [ZMOD 3] := by
    nth_rw 2 [← zero_add b]
    refine Int.ModEq.add ?_ rfl
    refine Dvd.dvd.modEq_zero_int ?_
    exact Int.dvd_mul_right 3 a

  -- a+b mod n is 0, then a mod n is -b
  have modeq_neg {a b: ℤ} (h: a+b ≡ 0 [ZMOD 3]): a ≡ -b [ZMOD 3] := by
    have: 0 = -b+b := by ring
    rw [this] at h
    exact Int.ModEq.add_right_cancel' b h

  -- if the equation holds, then 9 ∣ n, 3 ∣ x, 3 ∣ y
  have hdvd {a b m: ℤ}
    (heq: m^2 = 17 * a^4 - 32 * a^2 * b^2 + 41 * b^4):
    9 ∣ m ∧ 3 ∣ a ∧ 3 ∣ b := by
    -- extract multiples of 3 out.
    replace heq: m^2 = 3 * (6*a^4 - 10*a^2*b^2 + 14*b^4) +
      -(a^2+b^2)^2 := by
      rw [heq]; ring
    -- consider modulo 3
    have h1: m^2 ≡ -(a^2+b^2)^2 [ZMOD 3] := by
      rw [heq]
      apply modeq_add_fac
    -- then n mod 3 is 0, x^2 + y^2 mod 3 is 0
    obtain ⟨hm, hab⟩ := dvd_of_sq_mod3 h1
    -- moreover, x,y mod 3 is 0
    replace hab: a^2 ≡ -b^2 [ZMOD 3] := by
      apply modeq_neg (Dvd.dvd.zero_modEq_int hab).symm
    obtain ⟨ha,hb⟩ := dvd_of_sq_mod3 hab
    -- then easy to see 9 ∣ n.
    rcases ha with ⟨a0, ha0⟩
    rcases hb with ⟨b0, hb0⟩
    replace heq: m^2 = 81 * (
      3 * (6*a0^4 - 10*a0^2*b0^2 + 14*b0^4) -(a0^2+b0^2)^2 ) := by
      rw [heq, ha0, hb0]
      ring
    replace hm: 9^2 ∣ m^2 := by
      norm_num
      rw [heq]
      apply Int.dvd_mul_right
    rw [Int.pow_dvd_pow_iff (by norm_num)] at hm
    refine ⟨hm, ?_, ?_⟩
    · use a0
    · use b0

  -- if 3 ∣ a, then exist a0, 3a0 = a, with this a0 ≥ 0.
  have ex_of_dvd {a:ℕ} {c:ℤ} (hc: 0 < c) (h: c ∣ a):
    ∃ (a0:ℕ), a = c*a0 := by
    rcases h with ⟨aa, haa⟩
    use aa.natAbs
    have h1: 0 ≤ c*aa := by
      simp [← haa]
    have h2: 0 ≤ aa := by
      exact nonneg_of_mul_nonneg_right h1 hc
    rwa [Int.natAbs_of_nonneg h2]

  -- if (x,y,n) is a set of solution and n ≠ 0, we can reach a smaller solution.
  -- thus has a infinite descending chain, impossible.

  have h1 {m:ℕ} (mpos: 0 < m): ¬ ∃(a b:ℤ),
    (m^2:ℤ) = 17 * a^4 - 32 * a^2 * b^2 + 41 * b^4 := by
    -- suppose m is the smallest.
    induction' m using Nat.strong_induction_on with m ih
    rintro ⟨a, b, heq⟩
    obtain ⟨hm, ha, hb⟩ := hdvd heq
    -- then we can build a smaller one, thus contradcition.
    rcases (ex_of_dvd (by norm_num) hm) with ⟨m0, hm0⟩
    rcases ha with ⟨a0, rfl⟩
    rcases hb with ⟨b0, rfl⟩
    rw [hm0] at heq
    replace heq := hnxy heq
    zify at mpos
    rw [hm0] at mpos
    norm_cast at mpos
    have hh1: 0 < m0 := by
      exact Nat.pos_of_mul_pos_left mpos
    have hh2: m0 < m := by
      zify; rw [hm0]
      linarith only [hh1]
    specialize ih m0 hh2 hh1
    absurd ih
    use a0,b0

  -- so n can only be 0. and use same method, we can prove a,b are also 0.
  have h2 {a: ℕ} (apos: 0 < a): ¬ ∃b:ℤ,
    (0^2:ℤ) = 17*a^4 - 32*a^2*b^2 + 41*b^4 := by
    induction' a using Nat.strong_induction_on with a ih
    rintro ⟨b, heq⟩
    obtain ⟨_, ha, hb⟩ := hdvd heq
    rcases (ex_of_dvd (by norm_num) ha) with ⟨a0, ha0⟩
    rcases hb with ⟨b0, rfl⟩
    have: (0:ℤ) = 9*0 := by simp
    rw [ha0, this] at heq
    replace heq := hnxy heq
    norm_cast at ha0
    simp only [ha0, Nat.ofNat_pos, mul_pos_iff_of_pos_left] at apos
    specialize ih a0 (by linarith only [ha0, apos]) apos
    absurd ih
    use b0

  -- back to the problem
  constructor
  · intro heq
    -- n can only be 0
    have neq0: n = 0 := by
      rw [← Int.natAbs_sq n] at heq
      by_contra!
      replace: 0 < n.natAbs := by
        exact Int.natAbs_pos.mpr this
      specialize h1 this
      absurd h1
      use x,y
    -- then x can only be 0
    have xeq0: x = 0 := by
      by_contra!
      replace: 0 < x.natAbs := Int.natAbs_pos.mpr this
      specialize h2 this
      absurd h2
      use y
      rw [← neq0, heq]
      replace: x^4 = x.natAbs^4 := by
        have: x^4 = (x^2)^2 := by ring
        rw [this, ← Int.natAbs_sq x]
        ring
      simp [this]
    -- therefore y = 0
    have yeq0: y = 0 := by
      simp only [neq0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, xeq0, mul_zero, zero_mul, sub_self, zero_add,
        zero_eq_mul, pow_eq_zero_iff, false_or] at heq
      exact heq
    simp [neq0, xeq0, yeq0]
  · -- verification, trivial.
    simp only [Prod.mk_zero_zero, Prod.mk_eq_zero, and_imp]
    rintro rfl rfl rfl
    simp