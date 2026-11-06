import Mathlib

open Classical Finset

/- Given an integer $k \geq 2$, set $a_{1}=1$ and, for every integer $n \geq 2$, let $a_{n}$ be the smallest $x>a_{n-1}$ such that:

$$
x=1+\sum_{i=1}^{n-1}\left\lfloor\sqrt[k]{\frac{x}{a_{i}}}\right\rfloor .
$$

Prove that every prime occurs in the sequence $a_{1}, a_{2}, \ldots$.
(Bulgaria) Alexander Ivanov -/
theorem number_theory_605634
    {k : ℕ} (hk : 2 ≤ k)
    {a : ℕ → ℕ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, IsLeast {x | x > a (n - 1) ∧
      x = 1 + ∑ i ∈ Icc 1 (n - 1), ⌊(x / a i : ℝ) ^ (k : ℝ)⁻¹⌋₊} (a n)) :
    ∀ p, Nat.Prime p → ∃ n > 0, a n = p := by
  let B (n : ℕ) := n ≠ 0 ∧ ∀ p, Nat.factorization n p < k
  let b := Nat.nth B
  have sum_eq (c : ℕ) : c = ∑ b ∈ (Ioc 0 c).filter B, ⌊(c / b : ℝ) ^ (k : ℝ)⁻¹⌋₊ := by
    let d₁ (n : ℕ) := (Nat.factorization n).prod fun p n => p ^ (n / k)
    let d₂ (n : ℕ) := (Nat.factorization n).prod fun p n => p ^ (n % k)
    convert card_eq_sum_card_fiberwise (f := d₂) (s := Ioc 0 c) ?_ using 2 with b hb
    · simp
    · transitivity #(Ioc 0 ⌊(c / b : ℝ) ^ (k : ℝ)⁻¹⌋₊)
      · simp
      · apply Finset.card_nbij (b * · ^ k)
        · intro n hn
          simp at hb hn ⊢
          refine ⟨⟨⟨by omega, Nat.pos_pow_of_pos _ hn.1⟩, ?_⟩, ?_⟩
          · rw [Nat.le_floor_iff' (by omega)] at hn
            rify
            calc
              _ ≤ b * ((c / b : ℝ) ^ (k : ℝ)⁻¹) ^ k := by
                rw [mul_le_mul_left (by simp; omega),
                  pow_le_pow_iff_left₀ (by simp) (by positivity) (by omega)]
                exact hn.2
              _ = _ := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
                  inv_mul_cancel₀ (by simp; omega), Real.rpow_one]
                have : (b : ℝ) ≠ 0 := by simp; omega
                field_simp
          · simp only [d₂]
            conv_rhs => rw [← Nat.factorization_prod_pow_eq_self (n := b) (by omega)]
            transitivity ((b * n ^ k).factorization.mapRange (· % k) (by simp)).prod (· ^ ·)
            · simp [Finsupp.prod_mapRange_index]
            · congr 1
              ext p
              rw [Nat.factorization_mul _ (by simp; omega), Nat.factorization_pow]
              · simpa using Nat.mod_eq_of_lt (hb.2.2 _)
              · simp; omega
        · apply Set.injOn_of_injective
          simp [Function.Injective]
          intro a₁ a₂ h
          replace h := h.resolve_right (by simp at hb; omega)
          rwa [pow_left_inj₀ (by simp) (by simp) (by omega)] at h
        · refine fun n hn => ⟨d₁ n, ?_⟩
          simp at hn ⊢
          have mul_eq : b * d₁ n ^ k = n := by
            simp only [← hn.2, d₁, d₂]
            conv =>
              enter [1, 2]
              rw [Finsupp.prod, ← prod_pow,
                ← Finsupp.prod.eq_1 (g := fun p n => (p ^ (n / k)) ^ k)]
            rw [← Finsupp.prod_mul]
            conv =>
              enter [1, 2, p, n]
              rw [← pow_mul, ← pow_add, add_comm, Nat.div_add_mod']
            exact Nat.factorization_prod_pow_eq_self (by omega)
          refine ⟨⟨?_, ?_⟩, mul_eq⟩
          · simp [d₁, ← Nat.ne_zero_iff_zero_lt]
            rintro p hp - - p_eq -
            exact absurd p_eq hp.ne_zero
          · simp at hb
            apply Nat.le_floor
            rw [← pow_le_pow_iff_left₀ (n := k) (by simp) (by positivity) (by omega),
              ← mul_le_mul_left (a := (b : ℝ)) (by simp; omega)]
            norm_cast
            rw [mul_eq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
              inv_mul_cancel₀ (by simp; omega), Real.rpow_one]
            have : (b : ℝ) ≠ 0 := by simp; omega
            field_simp
            exact hn.1.2
    · simp
      intro n hn₁ hn₂
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [d₂, ← Nat.ne_zero_iff_zero_lt]
        rintro p hp - - p_eq
        exact absurd p_eq hp.ne_zero
      · refine trans ?_ hn₂
        simp [d₂]
        conv_rhs => rw [← Nat.factorization_prod_pow_eq_self (n := n) (by omega)]
        simp only [Finsupp.prod]
        refine Finset.prod_le_prod' fun q hq => ?_
        rw [pow_le_pow_iff_right₀ (by simp at hq; exact hq.1.one_lt)]
        apply Nat.mod_le
      · simp [d₂, B, Finsupp.prod]
        rw [Nat.factorization_prod]
        · constructor
          · simp [← ne_eq, Finset.prod_ne_zero_iff]
            simp
            rintro p hp - - p_eq
            exact absurd p_eq hp.ne_zero
          · intro p
            rw [Finset.sum_congr (g := fun q => fun₀ | q => n.factorization q % k) rfl]
            · rw [sum_apply']
              simp [Finsupp.single_apply]
              split_ifs with h
              · exact Nat.mod_lt _ (by omega)
              · omega
            · intro q hq
              simp at hq ⊢
              simp [hq.1]
        · simp
          rintro p hp - - p_eq
          exact absurd p_eq hp.ne_zero
  have primes_in_B : setOf Nat.Prime ⊆ setOf B := by
    refine fun p hp => ⟨hp.ne_zero, fun q => ?_⟩
    rw [Nat.Prime.factorization hp]
    by_cases q_eq : p = q
    · simp [q_eq]; omega
    · simp [Finsupp.single_eq_of_ne q_eq]; omega
  have infinite_B : (setOf B).Infinite :=
    Set.Infinite.mono primes_in_B Nat.infinite_setOf_prime
  replace sum_eq : ∀ (c : ℕ),
      c = ∑ i ∈ range (Nat.count B (c + 1)), ⌊(c / b i : ℝ) ^ (k : ℝ)⁻¹⌋₊ := by
    intro c
    convert sum_eq c using 1
    rw [Finset.sum_comp (f := fun b : ℕ => ⌊(c / b : ℝ) ^ (k : ℝ)⁻¹⌋₊) (g := b)]
    congr! 1 with n hn
    · ext n
      simp
      refine ⟨fun | ⟨i, hi, hi'⟩ => ?_, fun | ⟨⟨hn₁, hn₂⟩, hn₃⟩ => ?_⟩
      · simp [← hi', b]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have := (Nat.nth_mem_of_infinite infinite_B i).1
          omega
        · suffices Nat.nth B i < c + 1 by omega
          exact Nat.nth_lt_of_lt_count hi
        · exact Nat.nth_mem_of_infinite infinite_B _
      · exact ⟨Nat.count B n, Nat.count_strict_mono hn₃ (by omega), Nat.nth_count hn₃⟩
    · rw [smul_eq_mul, mul_left_eq_self₀]
      left
      suffices (range (Nat.count B (c + 1))).filter (b · = n) = {Nat.count B n} by
        simp [this]
      ext i
      simp
      refine ⟨fun | ⟨hi, hi'⟩ => ?_, fun hi => ?_⟩
      · rw [← hi']
        exact (Nat.count_nth (absurd · infinite_B)).symm
      · simp [hi] at hn ⊢
        exact ⟨Nat.count_strict_mono hn.2 (by omega), Nat.nth_count hn.2⟩
  suffices a_eq : ∀ i, a (i + 1) = b i by
    intro p hp
    have : b _ = p := Nat.nth_count (primes_in_B hp)
    rw [← a_eq] at this
    exact ⟨_, by simp, this⟩
  intro i
  induction' i using Nat.strongRecOn with i hi
  by_cases i_zero : i = 0
  · simp [Nat.nth_zero, ha1, B, b, i_zero]
    symm
    refine IsLeast.csInf_eq ⟨⟨by simp, fun p => ?_⟩, fun m hm => ?_⟩
    · simp; omega
    · simp at hm
      omega
  · apply IsLeast.unique (han (i + 1) (by omega))
    simp
    conv =>
      enter [1, 1, x]
      rw [show i = i + 1 - 1 by rfl, Nat.Icc_pred_right _ (by simp),
        Finset.sum_Ico_eq_sum_range, add_tsub_cancel_right, ← Finset.sum_coe_sort]
      conv =>
        enter [1]
        rw [show i = i - 1 + 1 by omega, hi (i - 1) (by omega)]
      conv =>
        enter [2, 2, 2, 2, x]
        rw [add_comm, hi _ (by simpa [-coe_mem] using x.2)]
      rw [Finset.sum_coe_sort (f := fun i => ⌊(x / (b i) : ℝ) ^ (k : ℝ)⁻¹⌋₊)]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (Nat.nth_lt_nth infinite_B).mpr (by omega)
    · conv_lhs => rw [sum_eq (b i)]
      have := (Nat.nth_mem_of_infinite infinite_B i).1
      rw [Nat.count_nth_succ_of_infinite infinite_B, Finset.sum_range_succ, add_comm,
        div_self (by simpa)]
      simp
    · intro c hc
      by_contra hc'
      simp at hc hc'
      conv_rhs at hc => enter [1]; rw [sum_eq c]
      have : Nat.count B (c + 1) = i := by
        rw [Nat.count_succ_eq_count]
        · replace hc' := le_of_lt hc'
          rw [← Nat.lt_nth_iff_count_lt infinite_B] at hc
          rw [← Nat.count_le_iff_le_nth infinite_B] at hc'
          omega
        · intro B_c
          have (j) (hj : j < i) : Nat.nth B j < c := by
            refine lt_of_le_of_lt ?_ hc.1
            rw [Nat.nth_le_nth infinite_B]
            omega
          have : b i ≤ c := (Nat.isLeast_nth_of_infinite infinite_B i).2 ⟨B_c, this⟩
          omega
      simp [this] at hc
