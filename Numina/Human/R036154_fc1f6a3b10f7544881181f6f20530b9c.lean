import Mathlib
open Nat

/-
Let x and y be two-digit integers such that y is obtained by reversing the digits of x.
The integers x and y satisfy x^2 - y^2 = m^2 for some positive integer m.
What is x + y + m?

We prove that's 154
Let x = 10 * a + b
Let y = 10 * b + a
-/

theorem AMC_Algebra_1158
  (x y a b m: ℤ)
  (hx : x = 10 * a + b)
  (hy : y = 10 * b + a)
  (heq : x * x - y * y = m * m)
  (ha1 : a > 0)
  (ha2 : a < 10)
  (hb1 : b > 0)
  (hb2 : b < 10)
  (hm : m > 0)
  : x + y + m = 154 := by
  let heq_z := heq
  let hx_tmp := hx
  let hy_tmp := hy

  qify at hx hy heq

  --Plug them into x^2 - y^2 = m^2, We get x^2 - y^2 = 9 * (11 * (a + b) * (a - b))
  have : (x : ℚ) * x - y * y = 9 * (11 * (a + b) * (a - b)) := by
    rw [hx, hy]
    ring_nf

  --Let k = 9 * (11 * (a + b) * (a - b))
  set k := 9 * (11 * ((a : ℚ) + b) * (a - b))
  rw [heq] at this

  --Because k = m*m, k is a square
  have hk : IsSquare k := ⟨m, this.symm⟩

  --And 9 is also a square
  have h9: IsSquare (9 : ℚ) := ⟨3, by linarith⟩

  --So their div 11 * ((a : ℚ) + b) * (a - b), is an square
  have hk9 : 11 * ((a : ℚ) + b) * (a - b) = k / 9 := by
    rw [← mul_left_inj' (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]: (9 : ℚ) ≠ 0)]
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.div_mul_cancel]
    rw [mul_comm]

  have h11mulSquare: IsSquare (11 * ((a : ℚ) + b) * (a - b)) := by
    rw [hk9]
    exact IsSquare.div hk h9

  rw [(by
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_sub]
    : (11 * ((a : ℚ) + b) * (a - b)) = (((11 * (a + b) * (a - b) : ℤ) : ℚ)))] at h11mulSquare
  rw [Rat.isSquare_intCast_iff] at h11mulSquare

  --Assume s square to m
  let ⟨s, hs⟩ := h11mulSquare

  --Than s can't be zero, because m is not zero
  have s_ne_0 : s ≠ 0 := by
    by_contra h0
    rw [h0] at hs
    qify at hs hm
    rw [hs] at hk9
    apply_fun (·*9) at hk9
    simp at hk9
    rw [← hk9] at this
    have := zero_eq_mul_self.mp (id (Eq.symm this))
    rw [this] at hm
    exact (Bool.eq_not_self (Rat.blt 0 0)).mp hm

  --So 11 must divides (a + b) * (a - b)， otherwise 11 * ((a : ℚ) + b) * (a - b) can't be a square.
  have h11_dvd_mul: 11 ∣ (a + b) * (a - b) := by
    refine Int.dvd_natAbs.mp ?_
    refine Int.ofNat_dvd_right.mpr ?_
    simp only [Int.reduceAbs]
    refine dvd_of_factorization_pos ?_
    by_contra h
    have : (11 * (a + b) * (a - b)).natAbs = (s * s).natAbs := by
      exact congrArg Int.natAbs hs
    rw [mul_assoc, Int.natAbs_mul, Int.natAbs_mul s] at this
    simp only [Int.reduceAbs] at this
    apply_fun (·.factorization 11) at this
    repeat rw [factorization_mul, Finsupp.add_apply] at this
    rw [Prime.factorization_self, h, add_zero] at this
    . exact  Nat.add_self_ne_one (s.natAbs.factorization 11) this.symm
    . exact properDivisors_eq_singleton_one_iff_prime.mp rfl
    . simp only [ne_eq, Int.natAbs_eq_zero]
      exact s_ne_0
    . exact Int.natAbs_ne_zero.mpr s_ne_0
    . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    . by_contra hmul0
      rw [Int.natAbs_eq_zero] at hmul0
      rw [mul_assoc] at hs
      rw [hmul0] at hs
      simp only [mul_zero, zero_eq_mul, or_self] at hs
      exact s_ne_0 hs

  --So either 11 divdes |a + b| or 11 divdes |a - b|
  apply Int.Prime.dvd_mul at h11_dvd_mul

  --We have |a - b| ≤ 8, becasue they are digits
  have ha_sub_b: (a - b).natAbs ≤ 8 := by
    rw [(by rfl: (8 : ℕ) = ((8 : ℤ).natAbs))]
    rw [Int.natAbs_le_iff_sq_le]
    have h1 : (a - b) - 8 ≤ 0 := by
      rw [(by simp only [Int.reduceSub] : (8 : ℤ) = 9 - 1)]
      apply Int.sub_nonpos_of_le
      refine Int.sub_le_sub ?_ hb1
      exact Int.lt_add_one_iff.mp ha2
    have h2 : (a - b) + 8 ≥ 0 := by
      suffices (a - b) ≥ -8 from by
        exact Lean.Omega.Int.add_nonnneg_iff_neg_le.mpr this
      rw [(by simp only [Int.reduceSub] : (-8 : ℤ) = 1 - 9)]
      refine Int.sub_le_sub ?_ ?_
      exact ha1
      exact Int.lt_add_one_iff.mp hb2
    set t := a - b
    have le : (t - 8) * (t + 8) ≤ 0 := by
      exact Int.mul_nonpos_of_nonpos_of_nonneg h1 h2
    rw [(by linarith: (t - 8) * (t + 8) = (t^2 - 8^2))] at le
    exact Int.le_of_sub_nonpos le

  cases' h11_dvd_mul with hdvd hdvd
  .
    --When 11 divdes |a + b|,We know that |a + b| ≤ 18, because they are digits
    have le_18: (a + b).natAbs ≤ 18 := by
      rw [(by rfl: (18 : ℕ) = ((18 : ℤ).natAbs))]
      rw [Int.natAbs_le_iff_sq_le]
      have h1 : (a + b) - 18 ≤ 0 := by
        rw [(by exact rfl : (18 : ℤ) = 9 + 9)]
        apply Int.sub_nonpos_of_le
        refine Int.add_le_add ?_ ?_
        exact Int.lt_add_one_iff.mp ha2
        exact Int.lt_add_one_iff.mp hb2
      have h2 : (a + b) + 18 ≥ 0 := by
        suffices (a + b) ≥ -18 from by
          exact Lean.Omega.Int.add_nonnneg_iff_neg_le.mpr this
        rw [(by exact rfl : (-18 : ℤ) = -9 + -9)]
        refine Int.add_le_add ?_ ?_
        suffices h : a > 0 from by
          exact ((by exact Int.toNat_eq_zero.mp rfl : 0 ≥ -9).trans
             (by exact Int.le_of_lt h : a ≥ 0))
        exact ha1
        suffices h : b > 0 from by
          exact ((by exact Int.toNat_eq_zero.mp rfl : 0 ≥ -9).trans
             (by exact Int.le_of_lt h : b ≥ 0))
        exact hb1
      set t := a + b
      have le : (t - 18) * (t + 18) ≤ 0 := by
        exact Int.mul_nonpos_of_nonpos_of_nonneg h1 h2
      rw [(by linarith: (t - 18) * (t + 18) = (t^2 - 18^2))] at le
      exact Int.le_of_sub_nonpos le

    --Assume 11 * d = |a + b|
    let ⟨d, hd⟩ := hdvd
    if heq_0 : d = 0 then
      --d can't be zero, that makes s be zero
      rw [heq_0] at hd
      simp only [mul_zero, Int.natAbs_eq_zero] at hd
      rw [hd] at hs
      simp only [mul_zero, zero_mul, zero_eq_mul, or_self] at hs
      exact (s_ne_0 hs).elim
    else if heq_1 : d = 1 then
      --When d = 1
      rw [heq_1] at hd
      simp only [mul_one] at hd
      --And we know a + b ≥ 0, cause they are both > 0
      have : a + b ≥ 0 := by
        refine Int.add_nonneg ?_ ?_
        exact Int.le_of_lt ha1
        exact Int.le_of_lt hb1
      apply_fun (fun x => (x : ℤ)) at hd
      rw [Int.natAbs_of_nonneg this] at hd
      --So a + b = 11
      simp only [cast_ofNat] at hd
      --So 11 * 11 * (a - b) is square
      rw [hd] at h11mulSquare
      have mul_square_square (m n : ℤ) (hmS : IsSquare m) (hm0 : m ≠ 0) (h : IsSquare (m * n)) : IsSquare n := by
        let ⟨a, ha⟩ := hmS
        let ⟨k, hk⟩ := h
        qify at hk
        apply_fun (· / ↑m) at hk
        rw [mul_comm, mul_div_assoc] at hk
        have : (m : ℚ) / (m : ℚ) = 1 := by
          refine (div_eq_one_iff_eq ?_).mpr rfl
          suffices h : m ≠ 0 from by
            exact Rat.num_ne_zero.mp hm0
          exact hm0
        rw [this, mul_one, ha] at hk
        suffices h : IsSquare (n : ℚ) from by
          exact Rat.isSquare_intCast_iff.mp h
        use (k: ℚ) / (a : ℚ)
        rw [hk]
        group
        rw [(by
          exact rfl
          : (-2 : ℤ) = (2 : ℤ) * -1)]
        rw [zpow_mul]
        simp
        left
        rw [zpow_two, pow_two]
      --So a - b is square
      have hSq: IsSquare (a - b) :=
        mul_square_square (11 * 11) (a - b) (by exact isSquare_mul_self 11)
          (by exact Ne.symm (OfNat.zero_ne_ofNat (11 * 11))) h11mulSquare

      --So a - b ≥ 0
      have ha_sub_b_nonneg: a - b ≥ 0 := by
        let ⟨s, hs⟩ := hSq
        rw [hs]
        rw [← pow_two]
        exact sq_nonneg s

      have : (a - b) = ((a - b).natAbs : ℤ) := Int.eq_natAbs_of_zero_le ha_sub_b_nonneg

      --So |a - b| is square
      rw [this] at hSq
      rw [Int.isSquare_natCast_iff] at hSq

      --Assume q * q = |a - b|
      let ⟨q, hq⟩ := hSq
      if h0 : q = 0 then
        --q can't be zero, that forces s to be zero
        rw [h0, mul_zero] at hq
        apply_fun (fun x => (x : ℤ)) at hq
        rw [← this] at hq
        rw [hq] at hs
        simp only [CharP.cast_eq_zero, mul_zero, zero_eq_mul, or_self] at hs
        exact (s_ne_0 hs).elim
      else if h1 : q = 1 then
        --When q = 1, a - b = |a - b| = 1
        rw [h1] at hq
        apply_fun (fun x => (x : ℤ)) at hq
        rw [← this] at hq
        simp only [mul_one, cast_one] at hq
        apply_fun (fun x => x + (a + b)) at hq
        nth_rw 2 [hd] at hq
        simp only [sub_add_add_cancel, Int.reduceAdd] at hq
        --We have showed that a + b = 11, so a = 6 and b = 5
        have (h1 : a + a = 12) (h2 : a + b = 11) : a = 6 ∧ b = 5 := by omega
        have := this hq hd
        rw [this.1, this.2] at hx_tmp hy_tmp
        simp only [Int.reduceMul, Int.reduceAdd] at hx_tmp hy_tmp
        rw [hx_tmp, hy_tmp] at heq_z
        simp only [Int.reduceMul, Int.reduceSub] at heq_z
        --Than we know m = 33
        have (m : ℤ) (h : 1089 = m * m)  (h1 : m > 0): m = 33 := by
          apply_fun (fun x => x.natAbs) at h
          rw [Int.natAbs_mul] at h
          simp only [Int.reduceAbs] at h
          rw [(by exact rfl: (1089  = 33 * 33))] at h
          apply_fun (fun x => x.sqrt) at h
          repeat rw [Nat.sqrt_eq] at h
          apply_fun (fun x => (x : ℤ)) at h
          rw [Int.natAbs_of_nonneg] at h
          simp only [cast_ofNat] at h
          exact h.symm
          exact Int.le_of_lt h1
        have hm33 : m = 33 := this m heq_z hm
        --So x + y + m = 154
        rw [hx_tmp, hy_tmp, hm33]
        simp only [Int.reduceAdd]
      else if h2 : q = 2 then
        --q can't be 2, that makes a not a integer
        rw [h2] at hq
        apply_fun (fun x => (x : ℤ)) at hq
        rw [← this] at hq
        simp only [reduceMul, cast_ofNat] at hq
        apply_fun (fun x => x + (a + b)) at hq
        nth_rw 2 [hd] at hq
        simp only [sub_add_add_cancel, Int.reduceAdd] at hq
        exact ((by omega : (h : a + a = 15) → False) hq).elim
      else
        --q can't > 2, that violates |a - b| ≤ 8
        have : q ≥ 2 := by
          change 2 ≤ q
          rw [Nat.two_le_iff]
          constructor
          . exact h0
          . exact h1
        have : q > 2 := Nat.lt_of_le_of_ne this (id (Ne.symm h2))
        have : q ≥ 3 := by exact this
        have : (a - b).natAbs ≥ 3 * 3 := by
          rw [hq]
          exact Nat.mul_le_mul this this
        simp only [reduceMul, ge_iff_le] at this
        have : 9 ≤ 8 := this.trans ha_sub_b
        exact ((by omega : (h : 9 ≤ 8) → False) this).elim
    else
      --d can't ≥ 2,  that doesn't meet the requirement of |a + b| ≤ 18
      have : d ≥ 2 := by
        change 2 ≤ d
        rw [Nat.two_le_iff]
        constructor
        . exact heq_0
        . exact heq_1
      have : 11 * d ≥ 22 := by
        rw [(by rfl: 22 = 11 * 2)]
        exact Nat.mul_le_mul_left 11 this
      rw [← hd, (by rfl: 22 = 18 + 4)] at this
      have := (Nat.add_le_add  le_18 (by exact NeZero.one_le: 4 ≥ 1)).trans this
      simp only [ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at this
  .
    --Because |a - b| ≤ 8, and s is not zero, 11 can't divdes |a - b|
    let ⟨k, hk⟩ := hdvd
    have k_ne_0 : k ≠ 0 := by
      by_contra hk0
      rw [hk0] at hk
      simp only [mul_zero, Int.natAbs_eq_zero] at hk
      rw [hk] at hs
      simp only [mul_zero, zero_eq_mul, or_self] at hs
      exact s_ne_0 hs

    rw [hk] at ha_sub_b
    have k_ge_1 : k ≥ 1 := by exact one_le_iff_ne_zero.mpr k_ne_0
    have k11_ge_11 : 11 * k ≥ 11 := by exact Nat.le_mul_of_pos_right 11 k_ge_1
    have := k11_ge_11.trans ha_sub_b
    rw [(by
      exact rfl
      : 11 = 8 + 3)] at this
    nth_rw 2 [← add_zero 8] at this
    apply Nat.le_of_add_le_add_left at this
    exact (not_succ_le_zero 2 this).elim
  . exact properDivisors_eq_singleton_one_iff_prime.mp rfl