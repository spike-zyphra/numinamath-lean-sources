import Mathlib

/- Problem 1. Consider $a$ and $b$ to be non-zero natural numbers. Prove that the equation


$$

x^{2}+(a+b)^{2} x+4 a b=1

$$


has rational solutions if and only if $a=b$. -/
theorem algebra_99742 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x : ℚ, x^2 + (a + b)^2 * x + 4 * a * b = 1) ↔ a = b
  := by
    constructor
    -- let x be a rational solution
    · intro ⟨x, xh⟩
      -- write the equation as x ^ 2 + s * x + p = 0, where s = (a + b) ^ 2 and p = 4ab - 1
      let s : ℚ := (a + b) ^ 2
      let p : ℚ := 4 * a * b - 1
      have quadratic_eq : 1 * (x * x) + s * x + p = 0 := by
        unfold s p
        linarith only [xh]

      -- 1 is not zero
      have q_ne : (1 : ℚ) ≠ 0 := by
        exact Rat.zero_ne_one.symm

      -- the quadratic has a root, so the disciminant is a square
      have disc_eq := (quadratic_eq_zero_iff_discrim_eq_sq q_ne _).mp quadratic_eq
      simp only [discrim, mul_one] at disc_eq

      -- the discriminant is an integer
      obtain ⟨z, zh⟩ : ∃ z : ℤ, z = s ^ 2 - 4 * p := by
        unfold s p
        refine ⟨((↑a + ↑b) ^ 2) ^ 2 - 4 * (4 * ↑a * ↑b - 1), ?_⟩
        norm_cast

      -- the discriminant is positive
      have hh : (0 : ℚ) ≤ z := by
        rw [zh, disc_eq]
        exact sq_nonneg (2 * x + s)
      rw [Int.cast_nonneg] at hh

      -- so the discriminant is a natural number
      obtain ⟨zn, znh⟩ : ∃ zn : ℕ, z = zn := Int.eq_ofNat_of_zero_le hh
      rw [znh] at zh
      simp only [Int.cast_natCast] at zh
      rw [←zh] at disc_eq

      -- the discriminant is a square
      have is_square : IsSquare (zn : ℚ) := by
        rw [disc_eq]
        exact IsSquare.sq (2 * x + s)
      simp only [Rat.isSquare_natCast_iff] at is_square

      -- so there are two natural numbers whose product is equal to the discriminant
      obtain ⟨n, nh⟩ := is_square

      -- 4p is positive
      have pos : 0 < 4 * p := by
        unfold p
        simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos]
        norm_cast
        have b_pos : 1 ≤ b := by omega
        rw [←mul_one 1]
        refine Nat.mul_lt_mul_of_lt_of_le ?_ b_pos b_pos
        omega

      -- the discriminant is less than s ^ 2
      have zn_s : zn < s ^ 2 := by
        linarith

      -- rewrite discriminant as a square
      rw [nh, Nat.cast_mul, ←pow_two] at zn_s

      -- s is a natural number
      let s' := (a + b) ^ 2
      have s_eq : s = s' := by
        unfold s s'
        norm_cast

      --rewrite inequality using natural numbers
      rw [s_eq] at zn_s
      norm_cast at zn_s

      -- then n < s'
      have n_le_s : n < s' := by
        refine (Nat.pow_lt_pow_iff_left ?_).mp zn_s
        omega

      -- write 4 * p as difference of squares
      have p_four : s ^ 2 - n ^ 2 = 4 * p := by
        norm_cast
        convert_to s ^ 2 - ↑(n * n) = 4 * p
        simp only [Nat.cast_pow, Nat.cast_mul, sub_right_inj]
        exact pow_two (n : ℚ)
        rw [←nh, zh]
        ring

      -- p is an integer
      let p_z : ℤ := 4 * a * b - 1
      have p_zh : p_z = p := by
        unfold p_z p
        norm_cast

      -- s is an integer
      let s_z : ℤ := (a + b) ^ 2
      have s_zh : s_z = s := by
        unfold s_z s
        norm_cast

      -- s is at least 1
      have one_le_s' : 1 ≤ s' := Nat.one_le_of_lt n_le_s

      -- casting to rationals distributes over s - 1
      have cast_sub_one : ((s' - 1 : ℕ) : ℚ) = (s' - (1 : ℕ) : ℚ) := Nat.cast_sub one_le_s'

      -- we have n ≤ s - 2
      have n_bound : n ≤ s' - 2 := by
        -- assume opposite
        by_contra h
        simp only [not_le] at h

        -- then we have that n ≤ s - 1
        have le_pred := Nat.le_pred_of_lt n_le_s

        -- then either n = s - 1 or n < s - 1
        cases' le_pred.eq_or_lt with aa bb
        -- consider n = s - 1
        · rw [aa] at p_four
          -- Get s + (s - 1) = 4p
          simp only [← s_zh, Nat.pred_eq_sub_one, cast_sub_one, ← s_eq, Nat.cast_one, sq_sub_sq,
            sub_sub_cancel, mul_one, ← p_zh] at p_four
          norm_cast at p_four

          -- then we have a contradiction, because LHS of is odd and RHS is even
          omega
        -- consider n < s - 1, then n ≤ s - 2
        · have le_pred_pred := Nat.le_pred_of_lt bb
          convert_to n ≤ s' - 2 at le_pred_pred

          -- contradiction
          refine absurd h ?_
          simp only [not_lt]
          exact le_pred_pred

      -- we have n ^ 2 ≤ (s - 2) ^ 2
      have n_sq_le : n ^ 2 ≤ (s' - 2) ^ 2 := Nat.pow_le_pow_of_le_left n_bound 2

      -- and n ^ 2 = (2 * x + s) ^ 2
      have n_sq_eq : n ^ 2 = (2 * x + s) ^ 2 := by
        rw [←disc_eq, nh]
        norm_cast
        exact Nat.pow_two n

      -- s is at least 2
      have two_le_s' : 2 ≤ s' := by
        by_contra hs'
        simp only [not_le] at hs'
        interval_cases eq_one : s'
        simp only [Nat.cast_one] at s_eq
        simp only [Nat.one_le_ofNat, Nat.sub_eq_zero_of_le, nonpos_iff_eq_zero] at n_bound
        subst n_bound nh znh
        rw [s_eq] at p_four
        simp only [one_pow, CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, sub_zero] at p_four
        unfold p at p_four
        have thonk := sub_eq_zero_of_eq p_four
        ring_nf at thonk
        rw [sub_eq_zero] at thonk
        norm_cast at thonk
        omega

      -- casting to rationals distributes over s - 2
      have cast_sub_two : ((s' - 2 : ℕ) : ℚ) = (s' - (2 : ℕ) : ℚ)
        := Nat.cast_sub two_le_s'

      -- consider the inequality as rationals
      qify at n_sq_le

      -- n ^ 2 = s ^ 2 - 4p
      have eqq : (n : ℚ) ^ 2 = s ^ 2 - 4 * p := by
        rw [n_sq_eq, ←disc_eq]
        exact zh

      -- then s ≤ 1 + p
      rw [eqq, cast_sub_two, sub_sq, ←s_eq] at n_sq_le
      simp only [Nat.cast_ofNat, tsub_le_iff_right] at n_sq_le
      have lee : 0 ≤ (s ^ 2 - 2 * s * 2 + 2 ^ 2 + 4 * p) - s ^ 2
        := (Rat.le_iff_sub_nonneg _ _).mp n_sq_le
      convert_to 0 ≤ 4 * (1 + p - s) at lee
      · ring
      simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, sub_nonneg] at lee

      -- (a - b) ^ 2 = 0
      unfold s p at lee

      have pow_le_zero : (a - b) ^ 2 ≤ (0 : ℚ) := by
        linarith

      have pow_eq_zero : (a - b) ^ 2 = (0 : ℚ) := le_antisymm pow_le_zero <| by positivity

      -- so a = b
      simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, sub_eq_zero, Nat.cast_inj] using pow_eq_zero

    -- if a = b
    · intro eq
      subst eq
      -- then -1 is a root
      refine ⟨-1, ?_⟩
      ring