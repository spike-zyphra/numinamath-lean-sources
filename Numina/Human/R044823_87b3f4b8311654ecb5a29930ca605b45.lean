import Mathlib

/- Let $n=2^{31}3^{19}.$  How many positive [integer](https://artofproblemsolving.com/wiki/index.php/Integer) [divisors](https://artofproblemsolving.com/wiki/index.php/Divisor) of $n^2$ are less than $n_{}$ but do not divide $n_{}$? -/

theorem number_theory_96513 {n : ℕ} (hn : n = 2^31 * 3^19) :
    ((Nat.divisors (n^2)).filter (fun x ↦ x < n ∧ ¬ (x ∣ n))).card = 589 := by

  -- First we partition the divisors of n² into those less than, equal to, and greater than n
  have hd : Nat.divisors (n^2) =
    (Nat.divisors (n^2)).filter (· < n) ∪ {n} ∪ (Nat.divisors (n^2)).filter (· > n) := by
    ext x
    constructor
    · intro hx
      rcases Nat.lt_trichotomy x n with h | h | h
      all_goals simp [hx, h]
    · intro hx
      rw [Finset.mem_union, Finset.mem_union] at hx
      rcases hx with ((h | h) | h)
      · exact Finset.mem_of_mem_filter x h
      · simp [Finset.mem_singleton.mp h, hn]; norm_num
      · exact Finset.mem_of_mem_filter x h

  -- We prove that divisors of n^2 less than n and greater than n are in the same number
  have bij_divisors : ((Nat.divisors (n^2)).filter (· < n)).card = ((Nat.divisors (n^2)).filter (· > n)).card := by
    apply Finset.card_eq_of_equiv

    -- Define the bijection: map x < n ↦ n² / x > n
    use (fun ⟨x, hx⟩ ↦ ⟨n^2 / x, by
      simp only [Nat.reducePow, Nat.reduceMul, gt_iff_lt, Finset.union_assoc, Finset.mem_filter,
        Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at *
      have : n ^ 2 / x ∣ n ^ 2 := by use x; exact Eq.symm (Nat.div_mul_cancel hx.1.1)
      refine ⟨⟨this, hx.1.2⟩, ?_⟩
      apply (Nat.lt_div_iff_mul_lt' hx.1.1 n).mpr
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_right hx.2 (by linarith)
    ⟩)

    all_goals
      intro ⟨x, hx⟩
      simp only [gt_iff_lt, Finset.mem_filter, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff] at hx

    · exact ⟨n^2 / x, by
        simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff]
        constructor; constructor
        · use x; exact Eq.symm (Nat.div_mul_cancel hx.1.1)
        · simp [hn]
        · apply (Nat.div_lt_iff_lt_mul (by linarith)).mpr
          rw [pow_two]
          exact Nat.mul_lt_mul_of_pos_left hx.2 (by linarith)⟩

    all_goals simp only [Subtype.mk.injEq, Nat.div_div_self hx.1.1 (by simp [hn])]

  -- We count the divisors of n and n^2
  have div_card : n.divisors.card = 640 := by
    rw [Nat.card_divisors (by simp [hn]), hn, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) (by decide), Nat.primeFactors_prime_pow (by norm_num) (by decide),
      Nat.factorization_mul_of_coprime (by norm_num), Nat.factorization_pow, Nat.factorization_pow,
      Finset.prod_union (by decide), Finset.prod_singleton, Finset.prod_singleton]
    norm_num

  have div_sq_card : (n^2).divisors.card = 63 * 39 := by
    rw [Nat.card_divisors (by simp [hn]), Nat.primeFactors_pow n (by norm_num), hn,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) (by decide), Nat.primeFactors_prime_pow (by norm_num) (by decide),
      mul_pow, ← pow_mul, ← pow_mul,
      Nat.factorization_mul_of_coprime (by norm_num), Nat.factorization_pow, Nat.factorization_pow,
      Finset.prod_union (by decide), Finset.prod_singleton, Finset.prod_singleton]
    norm_num

  -- The cardinality of our set is the difference between the cardinalities of the divisors of n ^ 2 less than n,
  -- and the divisors of n
  have : ∀ a, (n < a ∧ a < n ↔ False) := by
    intro a; simp only [iff_false, not_and, not_lt]; intro ha
    exact Nat.le_of_succ_le ha
  rw [hd, Finset.filter_union, Finset.filter_union, Finset.filter_filter, Finset.filter_filter]
  simp_rw [← and_assoc, and_self, this, false_and, Finset.filter_False, Finset.filter_singleton,
    Finset.union_empty, lt_self_iff_false, dvd_refl, not_true_eq_false, and_self, reduceIte, Finset.union_empty]
  rw [← Finset.filter_filter, Finset.filter_not, Finset.filter_filter, Finset.card_sdiff]

  · -- The divisors of n^2 that are also divisors of n and less than n are one less than the divisors of n
    have : (Finset.filter (fun a ↦ a < n ∧ a ∣ n) (n ^ 2).divisors).card = 639 := by
      suffices (Finset.filter (fun a ↦ a < n ∧ a ∣ n) (n ^ 2).divisors).card + 1 = n.divisors.card by
        rw [(by norm_num : 639 = 640 - 1), ← div_card, ← this]; simp
      rw [← Finset.card_singleton n, ← Finset.card_union_of_disjoint (by simp)]
      congr; ext x; constructor
      · intro hx
        simp only [Finset.mem_union, Finset.mem_filter, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Finset.mem_singleton] at hx
        rcases hx with (hx | hx)
        · simp [hx.2.2, (by simp [hn] : n ≠ 0)]
        · exact Finset.mem_filter.mpr (by simp [hx, hn])
      · intro hx
        by_cases hx' : x < n
        · simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_divisors, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Finset.mem_singleton]
          simp only [Nat.mem_divisors, ne_eq] at hx
          have : x ∣ n ^ 2 := by obtain ⟨k, hk⟩ := hx.1; use k * n; rw [← mul_assoc, ← hk]; exact pow_two n
          exact Or.inl ⟨⟨this, hx.2⟩, hx', hx.1⟩
        · simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_divisors, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Finset.mem_singleton]
          apply Nat.divisor_le at hx
          exact Or.inr (by linarith)
    rw [this]

    -- Now it is enough to count the number of divisors of n^2 less than n
    suffices (Finset.filter (fun a ↦ a < n) (n ^ 2).divisors).card = 1228 by rw [this]

    have :  (n ^ 2).divisors.card = (Finset.filter (fun x ↦ x < n) (n ^ 2).divisors ∪ {n}
      ∪ Finset.filter (fun x ↦ x > n) (n ^ 2).divisors).card := by congr

    -- But these are half of the divisors of n^2, rounded down
    rw [div_sq_card, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint (by simp),
      Finset.card_singleton, bij_divisors] at this
    norm_num at this
    linarith
    · simp only [gt_iff_lt, Finset.disjoint_union_left, Finset.disjoint_singleton_left,
      Finset.mem_filter, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, lt_self_iff_false, and_false, and_true, Finset.disjoint_filter]
      intro x hx hx'; linarith
  · intro x hx
    simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff] at hx
    exact Finset.mem_filter.mpr (by simp [hx.1, hx.2.1])