import Mathlib
/-- For how many values of $k$ is $12^{12}$ the least common multiple of the positive integers $6^6$, $8^8$, and $k$? -/
theorem number_theory_96877 : Set.ncard {k : ℕ | Nat.lcm (Nat.lcm (6^6 : ℕ) (8^8)) k = 12^12} = 25 := by
  have enum : {k : ℕ | Nat.lcm (Nat.lcm (6^6 : ℕ) (8^8)) k = 12^12} = {2^0 * 3^12, 2^1 * 3^12, 2^2 * 3^12, 2^3 * 3^12, 2^4 * 3^12, 2^5 * 3^12, 2^6 * 3^12, 2^7 * 3^12, 2^8 * 3^12, 2^9 * 3^12, 2^10 * 3^12, 2^11 * 3^12, 2^12 * 3^12, 2^13 * 3^12, 2^14 * 3^12, 2^15 * 3^12, 2^16 * 3^12, 2^17 * 3^12, 2^18 * 3^12, 2^19 * 3^12, 2^20 * 3^12, 2^21 * 3^12, 2^22 * 3^12, 2^23 * 3^12, 2^24 * 3^12} := by
    ext k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor <;> intro h
    · have lw := Nat.dvd_lcm_right ((6 ^ 6).lcm (8 ^ 8)) k
      rw [h] at lw
      have ww := (by norm_num: (6 ^ 6).lcm (8 ^ 8) = 2^24 * 3^6)
      rw [ww] at h; clear ww
      rw [(by norm_num: 12 ^ 12 = 2^24 * 3^12)] at lw
      have cpr : Nat.Coprime (2^24) (3^12) := by decide
      have kn : k ≠ 0 := by
        intro gh
        subst k
        simp only [Nat.reducePow, Nat.reduceMul, Nat.lcm_zero_right, Nat.factorization_zero] at h
        norm_num at h
      rw [←Nat.factorization_le_iff_dvd kn (by decide)] at lw
      -- we prove k.factorization 2 ≤ 24 so we can later enumerate
      have uu := lw 2
      rw [(by native_decide : Nat.factorization (2 ^ 24 * 3 ^ 12) 2 = 24)] at uu
      -- we also prove k.factorization 3 = 12
      have tp : k.factorization 3 = 12 := by
        apply (congr_arg (fun x => Nat.factorization x)) at h
        rw [Nat.factorization_lcm (by norm_num) kn] at h
        apply (congr_arg (fun x => x 3)) at h
        rw [(by native_decide : Nat.factorization (12 ^ 12) 3 = 12)] at h
        -- factorize
        have stp : ((2 ^ 24 * 3 ^ 6).factorization ⊔ k.factorization) 3 = (2 ^ 24 * 3 ^ 6).factorization 3 ⊔ k.factorization 3 := rfl
        rw [stp] at h
        clear stp
        rw [(by native_decide : Nat.factorization (2 ^ 24 * 3 ^ 6) 3 = 6)] at h
        -- conclude that it is 12
        by_cases tt : k.factorization 3 ≤ 6
        · simp only [tt, sup_of_le_left, Nat.reduceEqDiff] at h
        · have := sup_of_le_right (by exact Nat.le_of_not_ge tt : 6 ≤ k.factorization 3)
          rw [this] at h
          exact h
      -- prove that k has no other prime factors
      have everythingzero (a : ℕ) (h1 : a ≠ 2) (h2 : a ≠ 3) : k.factorization a = 0 := by
        have t1 := Nat.mem_primeFactorsList (n := k) (p := a) kn
        have t2 := Nat.factorization_eq_zero_iff k a
        have t3 : (a ∈ k.primeFactorsList) = (Nat.Prime a ∧ a ∣ k) := by exact propext t1
        apply (congr_arg (fun x => ¬x)) at t3
        simp only [kn, or_false] at t2
        rw [t2]
        rw [Decidable.not_and_iff_or_not] at t3
        rw [←t3]
        rw [Nat.factorization_le_iff_dvd kn (by norm_num)] at lw
        have sl := Nat.primeFactorsList_sublist_of_dvd lw (by norm_num)
        have ll : a ∉ (2 ^ 24 * 3 ^ 12).primeFactorsList → a ∉ k.primeFactorsList := by
          intro cnt cnt1
          exact cnt (by exact List.Sublist.mem cnt1 sl)
        apply ll
        rw [(by native_decide : Nat.primeFactorsList (2 ^ 24 * 3 ^ 12) = List.replicate 24 2 ++ List.replicate 12 3)]
        simp only [List.reduceReplicate, List.cons_append, List.nil_append, List.mem_cons, h1, h2,
          List.not_mem_nil, or_self, not_false_eq_true]
      -- split into 25 cases for k.factorization 2
      (obtain re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re | re : k.factorization 2 = 0 ∨ k.factorization 2 = 1 ∨ k.factorization 2 = 2 ∨ k.factorization 2 = 3 ∨ k.factorization 2 = 4 ∨ k.factorization 2 = 5 ∨ k.factorization 2 = 6 ∨ k.factorization 2 = 7 ∨ k.factorization 2 = 8 ∨ k.factorization 2 = 9 ∨ k.factorization 2 = 10 ∨ k.factorization 2 = 11 ∨ k.factorization 2 = 12 ∨ k.factorization 2 = 13 ∨ k.factorization 2 = 14 ∨ k.factorization 2 = 15 ∨ k.factorization 2 = 16 ∨ k.factorization 2 = 17 ∨ k.factorization 2 = 18 ∨ k.factorization 2 = 19 ∨ k.factorization 2 = 20 ∨ k.factorization 2 = 21 ∨ k.factorization 2 = 22 ∨ k.factorization 2 = 23 ∨ k.factorization 2 = 24 := by clear * - uu; omega) <;> /- this mess is to choose the right condition to satisfy -/ [(left);(right;left);(right;right;left);(right;right;right;left);(right;right;right;right;left);(right;right;right;right;right;left);(right;right;right;right;right;right;left);(right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;left);(right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right;right)]
      -- two numbers are equal if their factorizations are equal
      all_goals apply Nat.eq_of_factorization_eq kn (by decide)
      -- split by cases: p = 2, p = 3 and other p
      all_goals intro p; by_cases h1 : p = 2; (· subst p; rw [re]; native_decide); by_cases h2 : p = 3; (· subst p; rw [tp]; native_decide); rw [everythingzero _ h1 h2]; rw [←Nat.primeFactorsList_count_eq]; (have ty : (2 ^ (k.factorization 2) * 3 ^ 12).primeFactorsList = List.replicate (k.factorization 2) 2 ++ List.replicate 12 3 := by rw [re]; native_decide); rw [re] at ty; rw [ty]; simp only [List.replicate_one, List.reduceReplicate, List.cons_append, List.nil_append, ne_eq, h1, not_false_eq_true, List.count_cons_of_ne, h2, List.nodup_cons, List.not_mem_nil, List.nodup_nil, and_self, List.count_nil]
    -- all listed integers satisfy the condition
    · (obtain h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h := h) <;> subst k <;> norm_num
  rw [enum]
  (repeat rw [Set.ncard_insert_of_not_mem]) <;> try decide
  rw [Set.ncard_singleton]