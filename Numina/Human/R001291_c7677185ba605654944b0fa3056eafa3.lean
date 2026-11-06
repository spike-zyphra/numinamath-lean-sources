import Mathlib

theorem number_theory_22937 : Nat.card {x | ∃ n, x = n^2 ∧ x ∣ 46656} = 16 := by
  have neq : 46656 = 2 ^ 6 * 3 ^ 6 := by
    norm_num
  -- the cardinality of $\{0, 1, 2, 3\}$ is $4$
  have cardeq : Nat.card (Finset.Icc 0 3) = 4 := by
    have cardeq : Nat.card (Finset.Icc 0 3) = (Finset.Icc 0 3).card := by
      exact Nat.card_eq_finsetCard (Finset.Icc 0 3)
    rw [cardeq]
    simp only [Nat.card_Icc, Nat.reduceAdd, tsub_zero]
  -- define a function $f : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{x | \exists n, x = n^2 \and x | 46656\}$ by $f(a, b)=2^{2a}3^{2b}$
  let f : (Finset.Icc 0 3) × (Finset.Icc 0 3) → {x | ∃ n, x = n^2 ∧ x ∣ 46656} := by
    intro a
    -- suffices to show that $2^{2a}3^{2b}$ is a square and divides $46656$ for $a, b \in \{0, 1, 2, 3\}$
    use 2 ^ (2 * a.1.1) * 3 ^ (2 * a.2.1)
    use 2 ^ a.1.1 * 3 ^ a.2.1
    constructor
    ring
    rw [neq]
    -- $2^{2a}\mid 2^6$
    have dvd1 : 2 ^ (2 * a.1.1) ∣ 2 ^ 6 := by
      refine Nat.pow_dvd_pow_iff_le_right'.mpr ?_
      have le := a.1.2
      have : a.1.1 ≤ 3 := by
        exact Finset.mem_range_succ_iff.mp le
      linarith
    -- $3^{2b}\mid 3^6$
    have dvd2 : 3 ^ (2 * a.2.1) ∣ 3 ^ 6 := by
      refine Nat.pow_dvd_pow_iff_le_right'.mpr ?_
      have le := a.2.2
      have : a.2.1 ≤ 3 := by
        exact Finset.mem_range_succ_iff.mp le
      linarith
    exact Nat.mul_dvd_mul dvd1 dvd2
  -- $f$ is injective
  have inj : Function.Injective f := by
    -- we prove that if $f(a, b) = f(a', b')$ then $a = a'$ and $b = b'$
    intro a b fab
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, f] at fab
    have fab2 := fab
    -- $f(a, b).\mathrm{factorization} 2 = f(a', b').\mathrm{factorization} 2$, so $a = a'$
    apply congrArg (fun x ↦ x.factorization 2) at fab
    simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, mul_eq_zero, false_or, false_and, not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply] at fab
    norm_num at fab
    -- $f(a, b).\mathrm{factorization} 3 = f(a', b').\mathrm{factorization} 3$, so $b = b'$
    apply congrArg (fun x ↦ x.factorization 3) at fab2
    simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, mul_eq_zero, false_or, false_and, not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply] at fab2
    norm_num at fab2
    ext
    exact fab
    exact fab2
  -- $f$ is surjective
  have surj : Function.Surjective f := by
    intro x
    rcases x.2 with ⟨n, xeq, xdvd⟩
    -- $n \mid 2 ^3 * 3 ^3$
    have xdvd2 : x.1 ∣ (2 ^ 3 * 3 ^ 3) ^ 2 := by
      norm_num
      exact xdvd
    rw [xeq] at xdvd2
    apply (Nat.pow_dvd_pow_iff (by norm_num)).mp at xdvd2
    have nne : n ≠ 0 := by
      by_contra contra
      rw [contra] at xdvd2
      norm_num at xdvd2
    apply (Nat.factorization_le_iff_dvd nne (by norm_num)).mpr at xdvd2
    -- $n.factorization 2 \in \{0, 1, 2, 3\}
    have nfac2in : n.factorization 2 ∈ Finset.Icc 0 3 := by
      refine Finset.mem_Icc.mpr ?_
      constructor
      exact Nat.zero_le (n.factorization 2)
      have facle2 : n.factorization 2 ≤ (2 ^ 3 * 3 ^ 3).factorization 2 := by
        exact xdvd2 2
      -- $(2 ^ 3 * 3 ^ 3).factorization 2 = 3$
      have faceq : (2 ^ 3 * 3 ^ 3).factorization 2 = 3 := by
        simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, mul_eq_zero, false_or, false_and, not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
        norm_num
      rw [faceq] at facle2
      exact facle2
    -- $n.factorization 3 \in \{0, 1, 2, 3\}
    have nfac3in : n.factorization 3 ∈ Finset.Icc 0 3 := by
      refine Finset.mem_Icc.mpr ?_
      constructor
      exact Nat.zero_le (n.factorization 3)
      have facle2 : n.factorization 3 ≤ (2 ^ 3 * 3 ^ 3).factorization 3 := by
        exact xdvd2 3
      -- $(2 ^ 3 * 3 ^ 3).factorization 3 = 3$
      have faceq : (2 ^ 3 * 3 ^ 3).factorization 3 = 3 := by
        simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, mul_eq_zero, false_or, false_and, not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
        norm_num
      rw [faceq] at facle2
      exact facle2
    -- prove that $x = f(n.factorization 2, n.factorization 3)$
    use (⟨n.factorization 2, nfac2in⟩, ⟨n.factorization 3, nfac3in⟩) 
    simp only [Set.coe_setOf, Set.mem_setOf_eq, f]
    refine Eq.symm (Subtype.coe_eq_of_eq_mk ?_)
    simp only [Set.mem_setOf_eq]
    -- suffices to show $n = 2 ^{n.factorization 2} * 3 ^{n.factorization 3}$
    have neq : n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
      -- suffices to show that the factorization of $n$ and $2^{n.factorization 2} * 3^{n.factorization 3}$ are the same
      have nfaceq : n.factorization = (2 ^ (n.factorization 2) * 3 ^ (n.factorization 3)).factorization := by
        ext i
        -- if $i \leq 3$ then $n.factorization i = 2^{n.factorization 2} * 3^{n.factorization 3} i$
        if hi : i ≤ 3 then
          interval_cases i
          simp only [Nat.factorization_zero_right]
          simp only [Nat.factorization_one_right]
          simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply]
          norm_num
          simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply]
          norm_num
        -- if $i > 3$ then the factorization of both sides are zero
        else 
          rw [not_le] at hi
          -- $2.factorization i = 0$
          have fac2i : Nat.factorization 2 i = 0 := by
            have lt : 2 < i := by
              linarith
            exact Nat.factorization_eq_zero_of_lt lt
          -- $3.factorization i = 0$
          have fac3i : Nat.factorization 3 i = 0 := by
            exact Nat.factorization_eq_zero_of_lt hi
          -- $n.factorization i = 0$
          have facni : n.factorization i = 0 := by
            have facile := xdvd2 i
            simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply] at facile
            simp only [fac2i, mul_zero, fac3i, add_zero, nonpos_iff_eq_zero] at facile
            exact facile
          -- $n.factorization i = 2^{n.factorization 2} * 3^{n.factorization 3} i$
          simp only [facni, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
            not_false_eq_true, Nat.factorization_mul, Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Pi.natCast_def, Nat.cast_id, Pi.add_apply, Pi.mul_apply, fac2i, mul_zero, fac3i, add_zero]
      refine Nat.eq_of_factorization_eq nne ?_ ?_
      exact Ne.symm (NeZero.ne' (2 ^ n.factorization 2 * 3 ^ n.factorization 3))
      exact fun p => congrFun (congrArg DFunLike.coe nfaceq) p
    rw [xeq]
    nth_rw 1 [neq]
    ring
  -- construct a equivalence using $f$
  let equiv : (Finset.Icc 0 3) × (Finset.Icc 0 3) ≃ {x | ∃ n, x = n^2 ∧ x ∣ 46656} := by
    apply Equiv.ofBijective f 
    constructor
    exact inj
    exact surj
  -- so the cardinality of two sets is the same
  have cardeq2 : Nat.card ((Finset.Icc 0 3) × (Finset.Icc 0 3)) = Nat.card {x | ∃ n, x = n^2 ∧ x ∣ 46656} := by
    exact Nat.card_congr equiv
  rw [Nat.card_prod, cardeq] at cardeq2
  rw [← cardeq2]