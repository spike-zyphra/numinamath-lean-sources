import Mathlib

/- If $A$ and $B$ are relatively prime numbers, then the greatest common divisor of $A^{3}+B^{3}$ and $A^{2}+B^{2}$ is 1 or 2. -/
theorem number_theory_257808 (A B : ℤ) (hrel : IsCoprime A B) :
    Int.gcd (A ^ 3 + B ^ 3) (A ^ 2 + B ^ 2) = 1 ∨ Int.gcd (A ^ 3 + B ^ 3) (A ^ 2 + B ^ 2) = 2 := by

    -- First we show that w.l.o.g. we can assume A ≠ 0 and B ≠ 0
    wlog ha : A ≠ 0
    · -- Indeed, if A = 0, then B can only be ±1, then the result is trivial
      push_neg at ha
      rw [ha] at hrel ⊢
      have : B.natAbs = 1 := by
        have : Int.gcd 0 B = 1 := Int.isCoprime_iff_gcd_eq_one.mp hrel
        rwa [Int.gcd_zero_left] at this
      have : B = 1 ∨ B = -1 := by exact Int.natAbs_eq_natAbs_iff.mp this
      rcases this with rfl | rfl
      repeat left; simp

    wlog hb : B ≠ 0
    · -- Similarly, if B = 0, then A can only be ±1, then the result is trivial
      push_neg at hb
      rw [hb] at hrel ⊢
      have : A.natAbs = 1 := by
        have : Int.gcd A 0 = 1 := Int.isCoprime_iff_gcd_eq_one.mp hrel
        rwa [Int.gcd_zero_right] at this
      have : A = 1 ∨ A = -1 := by exact Int.natAbs_eq_natAbs_iff.mp this
      rcases this with rfl | rfl
      repeat left; simp

    -- Then we show some lemmas that we will need

    -- 1. A is coprime to A + B
    have ha_cp_sum : IsCoprime A (A + B) := by
      nth_rw 2 [show A = A * 1 by ring]
      exact IsCoprime.mul_add_left_right hrel 1

    -- 2. B is coprime to A + B
    have hb_cp_sum : IsCoprime B (A + B) := by
      nth_rw 2 [show B = B * 1 by ring]
      exact IsCoprime.add_mul_left_right (id (IsCoprime.symm hrel)) 1

    -- 3. A * B is coprime to A + B
    have hab_cp_sum : IsCoprime (A * B) (A + B) := by
      apply IsCoprime.symm
      exact IsCoprime.mul_right (id (IsCoprime.symm ha_cp_sum)) (id (IsCoprime.symm hb_cp_sum))

    -- 4. A * B is coprime to (A + B) ^ 2
    have hab_cp_sum_sq : IsCoprime (A * B) ((A + B) ^ 2) := by
      rw [pow_two]
      apply IsCoprime.symm
      apply IsCoprime.mul_left (id (IsCoprime.symm hab_cp_sum)) (id (IsCoprime.symm hab_cp_sum))

    -- Now we start the analysis.

    -- Step 1. we show any common divisor of A ^ 2 + B ^ 2 and A + B is at most 2
    have lem1 (d : ℕ) : (↑d ∣ A ^ 2 + B ^ 2) → (↑d ∣ A + B) → d ≤ 2 := by
      intro h1 h2   -- let d be a common divisor of A ^ 2 + B ^ 2 and A + B
      -- we have d also divides (A + B) ^ 2
      have h3 : ↑d ∣ (A + B) ^ 2 := by
        rw [pow_two]
        exact Dvd.dvd.mul_right h2 (A + B)

      -- as (A + B) ^ 2 = (A ^ 2 + B ^ 2) + 2 * (A * B), we deduce that d divides 2 * (A * B)
      rw [show (A + B) ^ 2 = (A ^ 2 + B ^ 2) + 2 * (A * B) by ring] at h3
      have h4 : ↑d ∣ 2 * (A * B) := by exact (Int.dvd_iff_dvd_of_dvd_add h3).mp h1

      -- we divide into cases whether d is even
      by_cases even_d : 2 ∣ d
      · -- if d is even, we write d = 2 * t
        have ⟨t, ht⟩ := even_d
        rw [ht] at h4   -- so 2 * t divides 2 * (A * B)
        rw [Nat.cast_mul] at h4
        -- it must be the case that t divides A * B
        have t_dvd_mul : ↑t ∣ A * B := by
          have ⟨k, hk⟩ := h4
          rw [mul_assoc] at hk
          have : A * B = t * k := by simp_all
          exact Dvd.intro k (id (Eq.symm this))
        -- as d = 2 * t is a divisor of A + B, t itself is also a divisor of A + B
        have t_dvd_add : ↑t ∣ A + B := by
          rw [ht] at h2
          rw [Nat.cast_mul] at h2
          exact dvd_of_mul_left_dvd h2
        -- so t is a common divisor of A + B and A * B, and we have t divides gcd (A + B) (A * B)
        have t_dvd_gcd : ↑t ∣ gcd (A + B) (A * B) := dvd_gcd t_dvd_add t_dvd_mul
        have : gcd (A + B) (A * B) = Int.gcd (A + B) (A * B) := by exact rfl
        rw [this] at t_dvd_gcd
        -- recall we have shown that A * B is coprime to A + B, so gcd (A + B) (A * B) = 1
        have : Int.gcd (A + B) (A * B) = 1 := Int.isCoprime_iff_gcd_eq_one.mp (id (IsCoprime.symm hab_cp_sum))
        rw [this] at t_dvd_gcd  -- so we deduce t ∣ 1
        -- then we have t ≤ 1 and d ≤ 2
        have : ↑t ≤ (1 : ℤ) := by apply Int.le_of_dvd; norm_num; exact t_dvd_gcd
        linarith
      · -- if d is odd, then d is coprime to 2
        have : Nat.Coprime 2 d := by
          refine Odd.coprime_two_left ?_
          refine Nat.odd_iff.mpr ?_
          simp_all
        have : IsCoprime (2 : ℤ) d := by exact Int.isCoprime_iff_gcd_eq_one.mpr this
        -- so d ∣ 2 * A * B implies d ∣ A * B
        have : ↑d ∣ A * B := by exact IsCoprime.dvd_of_dvd_mul_left (id (IsCoprime.symm this)) h4
        -- again, we have d divides gcd (A + B) (A * B) = 1
        have d_dvd_gcd : ↑d ∣ gcd (A + B) (A * B) := by exact dvd_gcd h2 this
        have : gcd (A + B) (A * B) = Int.gcd (A + B) (A * B) := by exact rfl
        rw [this] at d_dvd_gcd
        have : Int.gcd (A + B) (A * B) = 1 := Int.isCoprime_iff_gcd_eq_one.mp (id (IsCoprime.symm hab_cp_sum))
        rw [this] at d_dvd_gcd
        -- so in this case we have d ≤ 1
        have : ↑d ≤ (1 : ℤ) := by apply Int.le_of_dvd; norm_num; exact d_dvd_gcd
        linarith

    -- Step 2. we show the only common divisor of A ^ 2 + B ^ 2 and A ^ 2 - A * B + B ^ 2 is 1
    have lem2 (d : ℕ) : (↑d ∣ A ^ 2 + B ^ 2) → (↑d ∣ A ^ 2 - A * B + B ^ 2) → d = 1 := by
      intro h1 h2 -- let d be a common divisor of A ^ 2 + B ^ 2 and A ^ 2 - A * B + B ^ 2

      -- then d divides their difference A * B
      have d_dvd_mul : ↑d ∣ (A ^ 2 + B ^ 2) - (A ^ 2 - A * B + B ^ 2) := Int.dvd_sub h1 h2
      rw [show (A ^ 2 + B ^ 2) - (A ^ 2 - A * B + B ^ 2) = A * B by ring] at d_dvd_mul

      -- so d divides 2 * A * B
      have : ↑d ∣ 2 * (A * B) := by exact Dvd.dvd.mul_left d_dvd_mul 2

      -- and we deduce d ∣ (A ^ 2 + B ^ 2) + 2 * (A * B) = (A + B) ^ 2
      have d_dvd_sum_sq : (d : ℤ) ∣ (A ^ 2 + B ^ 2) + 2 * (A * B) := (Int.dvd_add_right h1).mpr this
      rw [show (A ^ 2 + B ^ 2) + 2 * (A * B) = (A + B) ^ 2 by ring] at d_dvd_sum_sq

      -- then d must divides gcd (A * B) ((A + B) ^ 2), which must be 1 as we have shown they are coprime
      have d_dvd_gcd : ↑d ∣ gcd (A * B) ((A + B) ^ 2) := dvd_gcd d_dvd_mul d_dvd_sum_sq
      have : gcd (A * B) ((A + B) ^ 2) = Int.gcd (A * B) ((A + B) ^ 2) := by exact rfl
      rw [this] at d_dvd_gcd
      have : Int.gcd (A * B) ((A + B) ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hab_cp_sum_sq
      rw [this] at d_dvd_gcd
      -- as d ∣ 1 we deduce d = 1
      norm_cast at d_dvd_gcd
      exact Nat.eq_one_of_dvd_one d_dvd_gcd

    -- Finally we prove the theorem
    -- we write A ^ 3 + B ^ 3 = (A + B) * (A ^ 2 - A * B + B ^ 2)
    rw [show A ^ 3 + B ^ 3 = (A + B) * (A ^ 2 - A * B + B ^ 2) by ring] at *
    -- and denote t₁ = A + B, t₂ = A ^ 2 + B ^ 2, t₃ = A ^ 2 - A * B + B ^ 2
    generalize (A + B) = t₁ at *
    generalize h2 : (A ^ 2 + B ^ 2) = t₂ at *
    generalize (A ^ 2 - A * B + B ^ 2) = t₃ at *
    -- so what we have shown is:
    -- 1. gcd t₂ t₁ ≤ 2
    -- 2. gcd t₂ t₃ = 1

    -- we need the fact that t₂ ≠ 0
    have t₂nz : t₂ ≠ 0 := by
      rw [← h2]
      exact IsCoprime.sq_add_sq_ne_zero hrel  -- because we assumed A, B ≠ 0

    -- we show that gcd t₂ (t₁ * t₃) ≤ gcd t₂ t₁ * gcd t₂ t₃
    have hgcd_le : Int.gcd t₂ (t₁ * t₃) ≤ Int.gcd t₂ t₁ * Int.gcd t₂ t₃ := by
      suffices h : gcd t₂ (t₁ * t₃) ≤ gcd t₂ t₁ * gcd t₂ t₃ by
        exact Int.ofNat_le.mp h
      have := gcd_mul_dvd_mul_gcd t₂ t₁ t₃
      apply Int.le_of_dvd ?_ this
      apply mul_pos
      · rw [show gcd t₂ t₁ = Int.gcd t₂ t₁ by exact rfl]
        norm_cast
        apply Int.gcd_pos_iff.mpr
        left
        assumption
      · rw [show gcd t₂ t₃ = Int.gcd t₂ t₃ by exact rfl]
        norm_cast
        apply Int.gcd_pos_iff.mpr
        left
        assumption

    -- then the previous lemmas imply that gcd t₂ t₁ ≤ 2 and gcd t₂ t₃ = 1
    have hgcd_2_1 : Int.gcd t₂ t₁ ≤ 2 := by
      have hleft : ↑(Int.gcd t₂ t₁) ∣ t₂ := by exact gcd_dvd_left t₂ t₁
      have hright : ↑(Int.gcd t₂ t₁) ∣ t₁ := by exact gcd_dvd_right t₂ t₁
      apply lem1 (Int.gcd t₂ t₁) hleft hright

    have hgcd_2_3 : Int.gcd t₂ t₃ = 1 := by
      have hleft : ↑(Int.gcd t₂ t₃) ∣ t₂ := by exact gcd_dvd_left t₂ t₃
      have hright : ↑(Int.gcd t₂ t₃) ∣ t₃ := by exact gcd_dvd_right t₂ t₃
      apply lem2 (Int.gcd t₂ t₃) hleft hright

    -- clearly these gcds are non-negative
    have : Int.gcd t₂ t₁ ≥ 0 := by exact Nat.zero_le (t₂.gcd t₁)

    have hgcd_le_2 : Int.gcd t₂ (t₁ * t₃) ≤ 2 := by
      have := Nat.mul_le_mul hgcd_2_1 (Nat.le_of_eq hgcd_2_3)
      simp at this
      linarith

    have : Int.gcd t₂ (t₁ * t₃) ≠ 0 := by
      refine Nat.ne_zero_iff_zero_lt.mpr ?_
      apply Int.gcd_pos_of_ne_zero_left (t₁ * t₃) t₂nz

    rw [Int.gcd_comm] at this
    rw [Int.gcd_comm] at hgcd_le_2
    generalize (t₁ * t₃).gcd t₂ = x at *
    -- writing gcd t₂ (t₁ * t₃) = x, we have shown that 0 ≤ x ≤ 2 and x ≠ 0
    interval_cases x
    -- so it must be that x = 1 or x = 2
    · contradiction
    · left; rfl
    · right; rfl
