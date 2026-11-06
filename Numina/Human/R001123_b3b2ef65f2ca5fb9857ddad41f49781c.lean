import Mathlib

/- Suppose that $x$ is a multiple of 6 (not necessarily positive). If the square of $x$ is less than 200, how many possible values of $x$ are there? -/
theorem algebra_20626 :
    Set.ncard {x : ℤ | 6 ∣ x ∧ x^2 < 200} = 5 := by
  -- $\{x : \mathbb{Z} | 6 \mid x \and x^2 < 200\} = \{-12, -6, 0, 6, 12\}$
  have seteq : {x : ℤ | 6 ∣ x ∧ x^2 < 200} = {-12, -6, 0, 6, 12} := by
    ext x
    constructor
    · -- if $6 \mid x \and x^2 < 200$ then $x = -12, -6, 0, 6, 12$
      intro xin
      rcases xin.1 with ⟨k, hk⟩
      -- since $6 \mid x$, there is $k$ such that $x = 6 * k$
      have xsqlt := xin.2
      rw [hk] at xsqlt
      -- by $x^2 < 200$ we have $k \leq 2$ and $k \geq -2$
      have kle : k ≤ 2 := by
        nlinarith
      have kge : k ≥ -2 := by
        nlinarith
      interval_cases k
      · -- if $k = -2$ then $x = -12$
        rw [hk]
        simp only [Int.reduceNeg, mul_neg, Int.reduceMul, Set.mem_insert_iff, neg_inj, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, neg_eq_zero, OfNat.ofNat_ne_zero, Set.mem_singleton_iff, or_self, or_false]
        aesop
      · -- if $k = -1$ then $x = -6$
        rw [hk]
        simp only [Int.reduceNeg, mul_neg, mul_one, Set.mem_insert_iff, neg_inj, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, neg_eq_zero, OfNat.ofNat_ne_zero, Set.mem_singleton_iff, or_self, or_false, or_true]
        aesop
      · -- if $k = 0$ then $x = 0$
        rw [hk]
        simp only [Int.reduceNeg, mul_zero, Set.mem_insert_iff, zero_eq_neg, OfNat.ofNat_ne_zero, OfNat.zero_ne_ofNat, Set.mem_singleton_iff, or_self, or_false, or_true]
      · -- if $k = 1$ then $x = 6$
        rw [hk]
        simp only [Int.reduceNeg, mul_one, Set.mem_insert_iff, OfNat.ofNat_ne_zero, Set.mem_singleton_iff, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, or_false, or_true]
      · -- if $k = 2$ then $x = 12$
        rw [hk]
        simp only [Int.reduceNeg, Int.reduceMul, Set.mem_insert_iff, OfNat.ofNat_ne_zero, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, Set.mem_singleton_iff, or_true]
    · -- if $x = -12, -6, 0, 6, 12$ then $6 \mid x \and x^2 < 200$
      intro xin
      rcases xin with xeq | xeq | xeq | xeq | xeq
      -- $x = -12$
      simp only [xeq, Int.reduceNeg, Set.mem_setOf_eq, dvd_neg, even_two, Even.neg_pow, Int.reducePow, Int.reduceLT, and_true]
      use 2
      exact rfl
      -- $x = -6$
      simp only [xeq, Int.reduceNeg, Set.mem_setOf_eq, dvd_neg, dvd_refl, even_two, Even.neg_pow, Int.reducePow, Int.reduceLT, and_self]
      -- $x = 0$
      simp only [xeq, Set.mem_setOf_eq, dvd_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.ofNat_pos, and_self]
      -- $x = 6$
      simp only [xeq, Set.mem_setOf_eq, dvd_refl, Int.reducePow, Int.reduceLT, and_self]
      -- $x = 12$
      rw [Set.mem_singleton_iff] at xeq
      simp only [xeq, Set.mem_setOf_eq, Int.reducePow, Int.reduceLT, and_true]
      use 2
      exact rfl
  -- so the cardinality of $\{x : \mathbb{Z} | 6 \mid x \and x^2 < 200\}$ = the cardinality of $\{-12, -6, 0, 6, 12\}$ = 5
  apply congrArg (fun s ↦ s.ncard) at seteq
  rw [seteq]
  repeat rw [Set.ncard_insert_eq_ite]
  simp only [Int.reduceNeg, Set.mem_insert_iff, neg_inj, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, neg_eq_zero, OfNat.ofNat_ne_zero, Set.mem_singleton_iff, or_self, ↓reduceIte, OfNat.zero_ne_ofNat, Set.ncard_singleton, Nat.reduceAdd]
  aesop
