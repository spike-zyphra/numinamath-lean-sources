import Mathlib

/- How many pairs of positive integers $(x, y)$ are there, those satisfy the identity $2^x - y^2 = 4$?

(A): $1$ (B): $2$ (C): $3$ (D): $4$ (E): None of the above. -/
/- How many pairs of positive integers $(x, y)$ are there, those satisfy the identity $2^x - y^2 = 4$?

(A): $1$ (B): $2$ (C): $3$ (D): $4$ (E): None of the above. -/
theorem negated_number_theory_71739 :
  {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (2 : ℤ)^x - y^2 = 4}.encard = 1 := by


  -- only solution of 2^x = 1+y^2 is x = 1, y = 1.
  have solve_eq {x y: ℕ} (heq: 2^x = 1 + y^2) (hx: x > 0):
    x=1 ∧ y=1 := by
    -- clearly y is odd.
    have h1: Even (2^x) := (Nat.even_pow' hx.ne').mpr (by norm_num)
    rw [heq] at h1
    replace h1: Odd y := by
      have: Odd (y^2) := by
        rw [add_comm 1, Nat.even_add_one] at h1
        exact Nat.not_even_iff_odd.mp h1
      exact Nat.Odd.of_mul_right this
    -- then y^2 mod 4 is 1
    have h2: y^2 % 4 = 1 := by
      zify
      refine Int.sq_mod_four_eq_one_of_odd ?_
      exact (Int.odd_coe_nat y).mpr h1
    -- then 2^x mod 4 is 2
    have h3: 2^x ≡ 2 [MOD 4] := by
      rw [heq]
      have: 2 = 1+1 := by norm_num
      nth_rw 2 [this]
      exact Nat.ModEq.add_left 1 h2
    -- thus x < 2, otherwise mod 4 is 0.
    have xlt: x < 2 := by
      by_contra! xge
      have h4: 2^x ≡ 0 [MOD 4] := by
        rw [← Nat.sub_add_cancel xge, pow_add]
        refine Nat.modEq_zero_iff_dvd.mpr ?_
        norm_num
      have := h4.symm.trans h3
      contradiction
    -- then x=1, y=1.
    have xeq: x = 1 := by omega
    have hy: y^2 = 1 := by
      rw [xeq] at heq
      linarith only [heq]
    have yeq: y = 1 := Nat.eq_one_of_mul_eq_one_left hy
    exact ⟨xeq,yeq⟩


  -- thus we claim only solution to original equation is x = 3, y = 2.
  have {x y: ℕ} (hx: x > 0) (hy: y > 0) (heq: 2^x = 4 + y^2): x = 3 ∧ y = 2 := by
    have h1: x > 2 := by
      have: 2^x > 2^2 := by
        linarith only [heq, sq_pos_of_pos hy]
      exact (pow_lt_pow_iff_right₀ (by norm_num)).mp this
    have h2: 4 ∣ 2^x := by
      have: 4 = 2^2 := by norm_num
      rw [this]
      refine Nat.pow_dvd_pow 2 h1.le
    -- then 4 divide y^2
    replace h2: 4 ∣ y^2 := by
      rw [heq] at h2
      exact Nat.dvd_add_self_left.mp h2
    replace h2: 2^2 ∣ y^2 := by
      norm_num [h2]
    rw [Nat.pow_dvd_pow_iff (by norm_num)] at h2
    -- 2 divide y, then y^2 = 4z^2
    rcases h2 with ⟨z,rfl⟩
    have h3: 4 + (2*z)^2 = 4*(1+z^2) := by ring
    -- cancel 4 from both sides, 2^(x-2) = 1 + z^2
    replace heq: 2^(x-2) = 1 + z^2 := by
      rw [h3, ← Nat.sub_add_cancel h1.le,
      add_comm _ 2, pow_add] at heq
      simpa only [Nat.reducePow, mul_eq_mul_left_iff,
      OfNat.ofNat_ne_zero, or_false] using heq
    specialize solve_eq heq (Nat.zero_lt_sub_of_lt h1)
    constructor <;> omega

  -- so only one solution.
  replace: {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (2 : ℤ)^x - y^2 = 4}
    = {(3,2)} := by
    ext ⟨x,y⟩
    simp only [gt_iff_lt, Set.mem_setOf_eq, Prod.mk_one_one,
    Set.mem_singleton_iff, Prod.mk_eq_one]
    constructor
    · rintro ⟨xpos,ypos,heq⟩
      replace heq: 2^x = 4 + (y:ℤ)^2 := by
        exact (add_eq_of_eq_sub heq.symm).symm
      norm_cast at heq
      simp only [Prod.mk.injEq]
      apply this xpos ypos heq
    · simp only [Prod.mk.injEq, and_imp]
      rintro rfl rfl
      norm_num

  simp [this]