import Mathlib

/-Suppose that $a$ and $b$ are positive integers such that $\operatorname{gcd}\left(a^{3}-b^{3},(a-b)^{3}\right)$ is not divisible by any perfect square except 1 . Given that $1 \leq a-b \leq 50$, compute the number of possible values of $a-b$ across all such $a, b$.-/
theorem number_theory_610804 :
  { d : ℤ | ∃ a > 0, ∃ b > 0, d = a - b ∧
    1 ≤ a - b ∧ a - b ≤ 50 ∧
    (∀ n > 1, ¬ n ^ 2 ∣ Int.gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3))
  }.encard = 23 := by

  -- this is a lemma in newer version of mathlib
  have natAbs_sub_of_nonneg_of_le {a b : Int} (h₁ : 0 ≤ b) (h₂ : b ≤ a) :
    (a - b).natAbs = a.natAbs - b.natAbs := by
    rw [← Int.ofNat_inj]
    rw [Int.natAbs_of_nonneg, Int.ofNat_sub, Int.natAbs_of_nonneg (Int.le_trans h₁ h₂), Int.natAbs_of_nonneg h₁]
    · rwa [← Int.ofNat_le, Int.natAbs_of_nonneg h₁, Int.natAbs_of_nonneg (Int.le_trans h₁ h₂)]
    · exact Int.sub_nonneg_of_le h₂

  -- recall that a positive integer is squarefree if it is not divisible by 
  -- any perfect square exacpt 1
  let SqFree (a : ℤ) : Prop := ∀ n > 1, ¬ n ^ 2 ∣ a

  -- so if a * b is squarefree, then so is a
  have sq_free_of_mul (a b : ℤ) : SqFree (a * b) → SqFree a := by
    intro h_sq_free_mul
    rintro n n_gt n_dvd
    have : n ^ 2 ∣ a * b := by exact Dvd.dvd.mul_right n_dvd b
    exact h_sq_free_mul n n_gt this

  -- indeed, there is a proposition of squarefree already in mathlib,
  -- we show it can imply our version
  have h_sq_free' (n : ℤ) : Squarefree n → SqFree n := by
    intro h_s t t_gt h_dvd
    rw [pow_two] at h_dvd
    have := h_s t h_dvd
    rcases Int.isUnit_iff.mp this with (rfl | rfl)
    linarith
    linarith

  -- we also need the lemma that gcd(m + n, m) = gcd(m, n)
  have lem_gcd_self_add {m n : ℤ} (hm : m > 0) (hn : n > 0) :
    Int.gcd (m + n) (m) = Int.gcd m n := by
      nth_rw 2 [Int.gcd_comm]
      unfold Int.gcd
      rw [Int.natAbs_add_of_nonneg (by linarith) (by linarith)]
      exact Nat.gcd_self_add_left m.natAbs n.natAbs

  -- Claim 1 : let a and b be positive integers. Then gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3)
  -- is squarefree iff gcd(a, b) = 1, a - b is square free, and a - b is not divisible by 3

  -- this is the first part of claim 1, that gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3)
  -- is squarefree implies gcd(a, b) = 1
  have claim_1_1 (a b : ℤ) (ha : a > 0) (_hb : b > 0) :
    SqFree (Int.gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3)) → Int.gcd a b = 1 := by
      intro h_sq_free
      by_contra! h
      -- if gcd(a, b) ≠ 1, then gcd(a, b) > 1
      have : (Int.gcd a b : ℤ) > 1 := by
        norm_cast
        apply lt_of_le_of_ne
        apply Nat.le_of_dvd
        refine Int.gcd_pos_of_ne_zero_left b ?_
        exact Ne.symm (Int.ne_of_lt ha)
        exact Nat.one_dvd (a.gcd b)
        exact id (Ne.symm h)
      -- in this case we show gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3) is divisible by 
      -- gcd(a, b)^3, so is not squarefree
      have h_dvd_1 : ((Int.gcd a b) : ℤ) ^ 3 ∣ a ^ 3 - b ^ 3 := by
        apply Int.dvd_sub
        all_goals refine (Int.pow_dvd_pow_iff ?_).mpr ?_
        all_goals norm_num
        exact Int.gcd_dvd_left
        exact Int.gcd_dvd_right
      have h_dvd_2 : ((Int.gcd a b) : ℤ) ^ 3 ∣ (a - b) ^ 3 := by
        refine (Int.pow_dvd_pow_iff ?_).mpr ?_
        norm_num
        apply dvd_sub
        exact Int.gcd_dvd_left
        exact Int.gcd_dvd_right
      have h_dvd_g : ((Int.gcd a b) : ℤ) ^ 3 ∣ (Int.gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3)) := by
        exact Int.dvd_gcd h_dvd_1 h_dvd_2
      apply h_sq_free (Int.gcd a b)
      norm_cast
      exact Int.ofNat_lt.mp this
      trans ((Int.gcd a b) : ℤ) ^ 3
      apply pow_dvd_pow
      norm_num
      exact h_dvd_g

  -- now we prove claim 1.
  have claim_1 (a b : ℤ) (ha : a > 0) (hb : b > 0) (h_d : 1 ≤ a - b) :
    SqFree (Int.gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3)) ↔
    (Int.gcd a b = 1) ∧ (SqFree (a - b)) ∧ (¬ 3 ∣ a - b) := by
      have h1 : (a - b) ^ 2 > 0 := by nlinarith
      have h2 : 3 * a * b > 0 := by nlinarith

      have a_eq_abs : a = a.natAbs := by symm; apply Int.natAbs_of_nonneg (by linarith)
      have b_eq_abs : b = b.natAbs := by symm; apply Int.natAbs_of_nonneg (by linarith)

      constructor
      · -- from left to right:
        intro h_sq_free_g -- assume gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3) is square free

        -- we already showed that gcd(a, b) = 1
        constructor
        · exact claim_1_1 a b ha hb h_sq_free_g

        -- then we write gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3) = (a-b) * gcd((a-b)^2, 3ab)
        rw [
          show a ^ 3 - b ^ 3 = (a - b) * ((a - b) ^ 2 + 3 * a * b) by ring,
          show (a - b) ^ 3 = (a - b) * (a - b) ^ 2 by ring,
          Int.gcd_mul_left,
          Nat.cast_mul,
          Int.natAbs_of_nonneg (by linarith),
          lem_gcd_self_add h1 h2
        ] at h_sq_free_g

        -- now we immediately get (a - b) is square free
        constructor
        · exact sq_free_of_mul (a - b) (↑(((a - b) ^ 2).gcd (3 * a * b))) h_sq_free_g

        -- finally, if 3 ∣ a - b, then 9 ∣ gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3),
        -- contradicting to that the latter is squarefree
        intro h_dvd
        have : 3 * 3 ∣ ((a - b) * ↑(((a - b) ^ 2).gcd (3 * a * b))) := by
          apply mul_dvd_mul
          exact h_dvd
          apply dvd_gcd
          exact dvd_pow h_dvd (by norm_num)
          rw [mul_assoc]; simp
        rw [← pow_two] at this
        exact h_sq_free_g 3 (by norm_num) this

      · -- from right to left:
        -- assume gcd(a, b) = 1, a - b is squarefree, and not divisible by 3
        rintro ⟨h_ab_coprime', h_sq_free_d, h_not_dvd_d⟩

        -- again we write gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3) = (a-b) * gcd((a-b)^2, 3ab)
        rw [
          show a ^ 3 - b ^ 3 = (a - b) * ((a - b) ^ 2 + 3 * a * b) by ring,
          show (a - b) ^ 3 = (a - b) * (a - b) ^ 2 by ring,
          Int.gcd_mul_left,
          Nat.cast_mul,
          Int.natAbs_of_nonneg (by linarith),
          lem_gcd_self_add h1 h2
        ]

        -- as a, b are coprime, we deduce (a-b), a are coprime
        have h_ab_coprime : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr h_ab_coprime'
        have : IsCoprime (a - b) a := by
          refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
          unfold Int.gcd
          rw [natAbs_sub_of_nonneg_of_le]
          rw [Nat.gcd_self_sub_left]
          exact Int.coprime_iff_nat_coprime.mp (id (IsCoprime.symm h_ab_coprime))

          · suffices h : b ≤ a by
              rw [a_eq_abs, b_eq_abs] at h
              norm_cast at h
            linarith
          exact Int.le_of_lt hb
          linarith

        -- also (a-b), b coprime
        have : IsCoprime (a - b) b := by
          refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
          unfold Int.gcd
          rw [natAbs_sub_of_nonneg_of_le]
          rw [Nat.gcd_sub_self_left]
          exact h_ab_coprime'

          · suffices h : b ≤ a by
              rw [a_eq_abs, b_eq_abs] at h
              norm_cast at h
            linarith
          exact Int.le_of_lt hb
          linarith

        -- therefore (a-b), (a*b) coprime
        have : IsCoprime (a - b) (a * b) := by
          apply IsCoprime.mul_right
          repeat assumption

        -- therefore (a-b)^2, (a*b) coprime
        have : IsCoprime ((a - b) ^ 2) (a * b) := by exact IsCoprime.pow_left this

        -- from 3 does not divide a - b, we deduce they are coprime
        have : IsCoprime (a - b) 3 := by
          refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
          have : Int.gcd (a - b) 3 ≤ (3 : ℤ).natAbs := by
            unfold Int.gcd
            apply Nat.gcd_le_right
            norm_num
          norm_num at this

          have : Int.gcd (a - b) 3 > 0 := by
            apply Int.gcd_pos_iff.mpr
            constructor
            all_goals linarith

          have h_dvd_1 : ↑(Int.gcd (a - b) 3) ∣ (a - b) := Int.gcd_dvd_left
          have h_dvd_2 : ↑(Int.gcd (a - b) 3) ∣ (3 : ℤ) := Int.gcd_dvd_right

          interval_cases Int.gcd (a - b) 3
          · rfl
          · norm_num at h_dvd_2
          · contradiction

        -- finally we deduce ((a - b) ^ 2) and (3 * (a * b)) are coprime
        have : IsCoprime ((a - b) ^ 2) 3 := by exact IsCoprime.pow_left this
        have : IsCoprime ((a - b) ^ 2) (3 * (a * b)) := by
          apply IsCoprime.mul_right
          repeat assumption

        -- so gcd ((a - b) ^ 2) (3 * (a * b)) = 1
        have : Int.gcd ((a - b) ^ 2) (3 * (a * b)) = 1 := by
          exact Int.isCoprime_iff_gcd_eq_one.mp this
        -- then (a - b) * gcd(...) = a - b is squarefree as we have assumed
        rw [← mul_assoc] at this
        rwa [this, Nat.cast_one, mul_one]

  -- using Claim 1, we show that the set of all possible values of a - b
  -- equals the set of c where 1 ≤ c ≤ 50 and c is squarefree, and 3 does not divide c
  have : { d : ℤ | ∃ a > 0, ∃ b > 0, d = a - b ∧
      1 ≤ a - b ∧ a - b ≤ 50 ∧
      (∀ n > 1, ¬ n ^ 2 ∣ Int.gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3))
    } = {c | 1 ≤ c ∧ c ≤ 50 ∧ SqFree c ∧ ¬ 3 ∣ c} := by
    ext c
    constructor
    · -- indeed, all possible values of a - b satisfy the condition of c by claim 1
      intro ⟨a, a_pos, b, b_pos, hc, h1, h50, h_sq_free'⟩

      have h_sq_free : SqFree (Int.gcd (a ^ 3 - b ^ 3) ((a - b) ^ 3)) := by
        unfold SqFree
        intro n n_gt h_dvd
        apply h_sq_free' n.natAbs
        suffices h : n.natAbs > (1 : ℤ) by exact Int.ofNat_lt.mp h
        rw [Int.natAbs_of_nonneg (by linarith)]
        exact n_gt
        have : n.natAbs ^ 2 = n ^ 2 := by
          exact Int.natAbs_pow_two n
        rw [← this] at h_dvd
        norm_cast at h_dvd

      constructor
      · linarith
      constructor
      · linarith

      have := claim_1 a b a_pos b_pos h1 |>.mp h_sq_free
      rw [hc]
      constructor
      · exact this.2.1
      · exact this.2.2

    · -- on the other hand, if c is square free and not divisible by 3,
      -- we can set a = c + 1, b = 1.
      intro ⟨h1, h50, h_sq_free, h_not_dvd⟩

      use c + 1
      constructor
      · linarith
      use 1
      constructor
      · norm_num
      constructor
      · ring
      constructor
      · linarith
      constructor
      · linarith

      have h_claim := claim_1 (c + 1) 1 (by linarith) (by linarith) (by linarith) |>.mpr
      have h_1 : Int.gcd (c + 1) 1 = 1 := by
        exact Int.gcd_one
      have h_2 : SqFree (c + 1 - 1) := by
        simp
        exact h_sq_free
      have h_3 : ¬ 3 ∣ c + 1 - 1 := by simp; exact h_not_dvd
      have h_claim := h_claim ⟨h_1, h_2, h_3⟩

      intro n n_gt h_dvd
      apply h_claim n
      linarith
      norm_cast

  rw [this]

  -- by a brute force enumeration, the set of all possible values of a = b 
  -- is the following 23 integers
  have : {c | 1 ≤ c ∧ c ≤ 50 ∧ SqFree c ∧ ¬ 3 ∣ c} =
    {1, 2, 5, 7, 10, 11, 13, 14, 17, 19, 22, 23, 26, 29, 31, 34, 35, 37, 38, 41, 43, 46, 47} := by
      ext c
      constructor
      · intro ⟨h1, h50, h_sq_free, h_not_dvd⟩
        match c with
        | Int.negSucc x =>
          have : Int.negSucc x < 0 := by exact Int.negSucc_lt_zero x
          linarith
        | Int.ofNat x => match x with
          | 0 => simp at h1
          | 3 | 6 | 9 | 12 | 15 | 18 | 21 | 24 | 27 | 30 | 33 | 36 | 39 | 42 | 45 | 48 =>
            all_goals norm_num at h_not_dvd
          | 4 | 8 | 16 | 20 | 28 | 32 | 40 | 44 =>
            exfalso; apply h_sq_free 2; all_goals norm_num
          | 25 | 50 => exfalso; apply h_sq_free 5; all_goals norm_num
          | 49 => exfalso; apply h_sq_free 7; all_goals norm_num
          | 1 | 2 | 5 | 7 | 10 | 11 | 13 | 14 | 17 | 19 | 22 | 23 | 26 | 29 | 31 | 34 | 35 | 37 | 38 | 41 | 43 | 46 | 47 => rw [Int.ofNat_eq_coe]; norm_cast
          | t + 51 => simp at h50; linarith
      ·
        rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        all_goals norm_num
        · apply h_sq_free'
          exact squarefree_one
        all_goals apply h_sq_free'
        all_goals norm_num
        · rw [show (10 : ℤ) = 2 * 5 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num
        · rw [show (14 : ℤ) = 2 * 7 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num
        · rw [show (22 : ℤ) = 2 * 11 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num
        · rw [show (26 : ℤ) = 2 * 13 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num
        · rw [show (34 : ℤ) = 2 * 17 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num
        · rw [show (35 : ℤ) = 5 * 7 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num
        · rw [show (38 : ℤ) = 2 * 19 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num
        · rw [show (46 : ℤ) = 2 * 23 by rfl]
          norm_cast
          apply Int.squarefree_natCast.mpr
          apply (Nat.squarefree_mul ?_).mpr
          constructor
          all_goals norm_num
          all_goals apply Prime.squarefree
          all_goals apply Nat.prime_iff.mp; norm_num

  rw [this]

  -- this gives the answer 23
  rw [Set.encard_eq_coe_toFinset_card]
  rfl
