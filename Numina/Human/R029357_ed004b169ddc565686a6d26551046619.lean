import Mathlib

/- For each positive integer $n$, let $a_n$ be the least positive integer multiple
of $23$ such that $a_n \equiv 1 \pmod{2^n}$. Find the number of positive integers $n$
less than or equal to $1000$ that satisfy $a_n = a_{n+1}$. -/
theorem number_theory_98658 (a : ℕ → ℕ)
    (ha : ∀ n, 0 < n → IsLeast {x | 0 < x ∧ 23 ∣ x ∧ x ≡ 1 [MOD 2^n]} (a n)) :
    Set.ncard {n | 0 < n ∧ n ≤ 1000 ∧ a n = a (n + 1)} = 363 := by
  -- If a number x satisfies the conditions above, then x = 2^n * k + 1 for some k,
  -- and so k = (-2^n)⁻¹ mod 23. Note that since 23 is prime, by Fermat's Theorem
  -- we have 2^22 ≡ 1 mod 23. In fact, 2^11 ≡ 1 mod 23 as well, which we can verify:
  have pow_two_11 : (2^11 : ZMod 23) = 1 := by decide

  -- Unfortunately Lean 1.15 cannot seem to compute these with `simp` or `rfl`
  -- due to a bug(?), so here they are:
  let neg_inv_two_pow : ZMod 11 → ZMod 23
    | 0 => 22
    | 1 => 11
    | 2 => 17
    | 3 => 20
    | 4 => 10
    | 5 => 5
    | 6 => 14
    | 7 => 7
    | 8 => 15
    | 9 => 19
    | 10 => 21

  -- We can verify that these are indeed equal to (-2^n)⁻¹ mod 23 by checking all 11 cases with
  -- a straightforward calculation.
  have neg_inv_two_pow_eq (n : ℕ) : neg_inv_two_pow ↑n = (-2^n)⁻¹ := by
    have (n : ZMod 11) : neg_inv_two_pow n = (-2^n.val)⁻¹ := by
      rw [eq_comm]
      refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
      fin_cases n <;> simp [neg_inv_two_pow] <;> decide
    rw [this]
    have : (2^n : ZMod 23) = 2^(n : ZMod 11).val := by
      rw [ZMod.val_natCast]
      nth_rw 1 [← Nat.div_add_mod' n 11]
      rw [mul_comm, pow_add, pow_mul, pow_two_11]
      simp
    rw [this]

  -- Now, since a_n is the least such x, then a_n = 2^n * k + 1, where
  -- k = neg_inv_two_pow (n % 11).val as a natural number (the least such k mod 23).
  let k (n : ZMod 11) : ℕ := (neg_inv_two_pow ↑n).val

  -- And we can show that this characterizes a_n.
  have h_a_k {n} (hn : 0 < n) : a n = 2^n * k ↑n + 1 := by
    -- As stated above, if x satisfies the conditions, then x = 2^n * k + 1 for some k with k = (-2^n)⁻¹ mod 23.
    have cond_prop {x} (hpos : 0 < x) (hdiv : 23 ∣ x) (hmod : x ≡ 1 [MOD 2^n]) : ∃ k', x = 2^n * k' + 1 ∧ (k' : ZMod 23) = neg_inv_two_pow ↑n := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (show 1 ≤ x by omega)] at hmod
      obtain ⟨k', hk'⟩ := hmod
      use k'
      and_intros
      . omega
      . rw [neg_inv_two_pow_eq, eq_comm]
        refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
        rw [Nat.sub_eq_iff_eq_add (show 1 ≤ x by omega)] at hk'
        apply_fun (fun x => (x : ZMod 23)) at hk'
        simp at hk'
        rw [(ZMod.natCast_zmod_eq_zero_iff_dvd x 23).mpr hdiv, eq_comm, ← eq_sub_iff_add_eq',
          zero_sub, ← neg_mul, eq_comm] at hk'
        exact hk'
    -- We show that 2^n * k ↑n + 1 is the least such x, and therefore it is equal to a_n.
    rw [← IsLeast.isLeast_iff_eq (ha n hn)]
    constructor
    . and_intros
      . simp
      . have neg_two_pow_IsUnit : IsUnit (-2^n : ZMod 23) := by
          rw [IsUnit.neg_iff]
          refine IsUnit.pow _ ?_
          rw [show (2 : ZMod 23) = ↑(2 : ℕ) by simp, ZMod.isUnit_iff_coprime]
          norm_num
        rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
        simp [k]
        rw [neg_inv_two_pow_eq, ← eq_sub_iff_add_eq', zero_sub, ← neg_mul, ZMod.mul_inv_of_unit _ neg_two_pow_IsUnit]
      . refine Nat.ModEq.add_right 1 ?_
        rw [Nat.modEq_zero_iff_dvd]
        exact Nat.dvd_mul_right _ _
    . rintro x ⟨hpos, hdiv, hmod⟩
      obtain ⟨k', hk'x, hk'mod⟩ := cond_prop hpos hdiv hmod
      rw [hk'x]
      simp [k]
      rw [← hk'mod]
      cases le_or_gt (k' : ZMod 23).val k' with
      | inl h => exact h
      | inr h =>
        exfalso
        obtain ⟨m, hm⟩ : 23 ∣ (k' : ZMod 23).val - k' := by
          rw [← Nat.modEq_iff_dvd' (by linarith), ← ZMod.eq_iff_modEq_nat]
          simp
        rw [Nat.sub_eq_iff_eq_add (by linarith)] at hm
        have : m ≥ 1 := by linarith
        have : (k' : ZMod 23).val < 23 := ZMod.val_lt _
        linarith

  -- Using the above we can simplify a n = a (n + 1) to k n = 2 * k (n + 1)
  have h_a_eq {n} (hn : 0 < n) : a n = a (n + 1) ↔ k ↑n = 2 * k (↑n + 1) := by
    simp [h_a_k, hn, pow_succ]
    rw [mul_assoc, Nat.mul_left_cancel_iff (Nat.two_pow_pos n)]

  -- Note that k only depends on n mod 11, so by inspection this true exactly when
  -- n % 11 is 0, 3, 4, or 6.
  have a_eq_next_iff_n_mod {n} (hn: 0 < n): a n = a (n + 1) ↔ ↑(n % 11) ∈ ({0, 3, 4, 6} : Finset (Fin 11)) := by
    refine Iff.trans (h_a_eq hn) ?_
    have k_eq {n} (hn : n ∈ Finset.range 11) : k n = 2 * k (n + 1) ↔ ↑n ∈ ({0, 3, 4, 6} : Finset (Fin 11)) := by
      fin_cases hn <;> simp [k, neg_inv_two_pow] <;> decide
    rw [← k_eq (show n % 11 ∈ Finset.range 11 by simp [Finset.mem_range]; exact Nat.mod_lt n (by simp))]
    simp

  -- Note that 1001 = 91 * 11, so [0, 1001) has each of the numbers n % 11 exactly 91 times. Let's
  -- split off 0 and handle it separately, and write the rest as a Finset.
  have hset_split : {n | 0 < n ∧ n ≤ 1000 ∧ a n = a (n + 1)} = { n ∈ Finset.range 1001 | ↑(n % 11) ∈ ({0, 3, 4, 6} : Finset (Fin 11)) } \ {0} := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_sdiff, Finset.coe_filter, Finset.mem_range, Finset.coe_singleton, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    . rintro ⟨hn, hmax, ha⟩
      exact ⟨⟨by linarith, (a_eq_next_iff_n_mod hn).mp ha⟩, by linarith⟩
    . rintro ⟨⟨hmax, hrem⟩, hn⟩
      have hn : 0 < n := by omega
      exact ⟨hn, by linarith, (a_eq_next_iff_n_mod hn).mpr hrem⟩

  -- Now we use the standard divmod equivalence to write the set as a product, which we can easily compute the cardinality of.
  have hset_equiv : ∀ n, n ∈ { n ∈ Finset.range 1001 | ↑(n % 11) ∈ ({0, 3, 4, 6} : Finset (Fin 11)) } ↔ Nat.divModEquiv 11 n ∈ Finset.range 91 ×ˢ ({0, 3, 4, 6} : Finset (Fin 11)) := by
    intro n
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_range, Nat.divModEquiv, Equiv.coe_fn_mk, Finset.mem_product]
    rw [show (↑(n % 11) : Fin 11) = ↑n by rw [Fin.natCast_def, Fin.natCast_def, Fin.mk.injEq, Nat.mod_mod]]
    rw [Nat.div_lt_iff_lt_mul (show 0 < 11 by norm_num)]

  rw [hset_split, Set.ncard_coe_Finset, Finset.card_sdiff (by simp), Finset.card_singleton]
  rw [Finset.card_equiv (Nat.divModEquiv 11) hset_equiv]
  simp