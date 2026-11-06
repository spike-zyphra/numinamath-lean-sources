import Mathlib

/- Prove that there exist infinitely many positive integers $n$ such that $n^{2}+1$ has a prime divisor greater than $2 n+\sqrt{2 n}$. -/
theorem number_theory_23791 :
    {n : ℕ | n > 0 ∧ ∃ p : ℕ, Nat.Prime p ∧ p ∣ (n ^ 2 + 1) ∧ p > 2 * n + Real.sqrt (2 * n)}.Infinite := by
  -- Use the fact that there are infinitely many primes p ≡ 1 (mod 8).
  have h₀ := @Nat.infinite_setOf_prime_modEq_one 8 (by norm_num)
  -- Show that for such primes p, there exists n such that p | n² + 1 and small enough.
  have h₁ (p : ℕ) (hp₁ : Nat.Prime p) (hp₂ : p ≡ 1 [MOD 8]) : ∃ n, p ∣ n ^ 2 + 1 ∧ n ≤ (p - 1) / 2 := by
    -- Use Wilson's theorem to show that (p - 1)! ≡ -1 (mod p).
    have h₁ := @ZMod.wilsons_lemma p (by rw [fact_iff]; exact hp₁)
    replace h₁ : (((p - 1).factorial : ℕ) : ZMod p) = (p - 1 : ℤ) := by
      rw [h₁, show (p - 1 : ℤ) = (p - 1 : ℕ) by apply Int.subNatNat_of_le (Nat.succ_le_of_lt hp₁.pos), show (-1 : ZMod p) = (-1 : ℤ) by simp]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp
      norm_cast
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hp₁.pos)]
    zify at h₁
    -- Show that (p - 1)! ≡ ((p - 1) / 2)! (mod p).
    have h₂ : (∏ k ∈ Finset.Ico 1 ((p + 1) / 2), k) * (∏ k ∈ Finset.Ico ((p + 1) / 2) p, k) = (p - 1).factorial := by
      rw [Finset.prod_Ico_consecutive, <-Finset.prod_Ico_id_eq_factorial, Nat.sub_add_cancel (Nat.succ_le_of_lt hp₁.pos)]
      have h₂ : p ≥ 2 := Nat.Prime.two_le hp₁
      omega
      omega
    replace hp₁ : Nat.Prime p ∧ p ≠ 2 := by
      refine ⟨hp₁, ?_⟩
      by_contra!
      rw [this] at hp₂
      symm at hp₂
      rw [Nat.modEq_iff_dvd'] at hp₂
      norm_num at hp₂
      norm_num
    have h₃ : (∏ k ∈ Finset.Ico 1 ((p + 1) / 2), k) * (∏ k ∈ Finset.Ico 1 ((p + 1) / 2), (p - k)) = (p - 1).factorial := by
      rw [@Finset.prod_Ico_reflect _ _ (fun k => k) 1 ((p + 1) / 2) p]
      have h₃ : Even (p + 1) := by
        have h₃ := Nat.Prime.odd_of_ne_two hp₁.1 hp₁.2
        rw [Nat.even_add_one]
        simp [h₃]
      rw [even_iff_two_dvd] at h₃
      have h₄ : (p + 1) - (p + 1) / 2 = (p + 1) / 2 := by
        omega
      rw [h₄]
      simp [h₂]
      omega
    replace hp₂ : ∃ k, p = 8 * k + 1 := by
      symm at hp₂
      rw [Nat.modEq_iff_dvd', dvd_iff_exists_eq_mul_right] at hp₂
      obtain ⟨k, hp₂⟩ := hp₂
      use k
      rw [<-hp₂, Nat.sub_add_cancel]
      all_goals
        linarith only [Nat.Prime.two_le hp₁.1]
    obtain ⟨k, hp₂⟩ := hp₂
    have h₄ : (∏ k ∈ Finset.Ico 1 ((p + 1) / 2), (p - k) : ZMod p) = (∏ k ∈ Finset.Ico 1 ((p + 1) / 2), k : ZMod p) * ((-1) ^ ((p + 1) / 2 - 1) : ℤ) := by
      simp
      conv =>
        lhs
        congr
        . skip
        . ext n
          rw [<-mul_neg_one]
      rw [<-Finset.prod_mul_pow_card]
      simp
    rw [show (-1) ^ ((p + 1) / 2 - 1) = 1 by rw [neg_one_pow_eq_one_iff_even, hp₂, show (8 * k + 1 + 1) / 2 - 1 = 4 * k by omega, even_iff_two_dvd]; omega; norm_num] at h₄
    simp at h₄
    have h₅ : (∏ k ∈ Finset.Ico 1 ((p + 1) / 2), (p - k)) ^ 2 ≡ p - 1 [ZMOD p] := by
      rw [<-ZMod.intCast_eq_intCast_iff]
      zify
      rw [pow_two, <-h₁]
      norm_cast at h₄ ⊢
      rw [<-h₃]
      simp
      congrm ?_ * ?_
      . rw [<-h₄, Finset.prod_congr]
        . rfl
        . intro x hx
          rw [Finset.mem_Ico] at hx
          rw [<-add_eq_zero_iff_eq_neg]
          norm_cast
          rw [Nat.sub_add_cancel]
          simp
          omega
      . rfl
    let m := (∏ k ∈ Finset.Ico 1 ((p + 1) / 2), (p - k)) % p -- We have 0 ≤ m < p.
    replace h₅ : m ^ 2 ≡ p - 1 [ZMOD p] := by
      simp [m]
      refine Int.ModEq.trans ?_ h₅
      rw [<-ZMod.intCast_eq_intCast_iff]
      simp
    have h₆ : (p - m : ℕ) ^ 2 ≡ p - 1 [ZMOD p] := by
      refine Int.ModEq.trans ?_ h₅
      rw [show (p - m : ℕ) = (p - m : ℤ) by norm_cast; rw [Int.subNatNat_of_le]; simp [m]; apply le_of_lt; apply Nat.mod_lt; exact hp₁.1.pos]
      rw [Int.modEq_iff_dvd, sq_sub_sq]
      simp
    let n := min m (p - m)
    have h₇ : n ^ 2 ≡ p - 1 [ZMOD p] := by
      cases Nat.le_total m (p - m) with
      | inl h₈ =>
        simp only [n]
        rw [min_eq_left h₈]
        exact h₅
      | inr h₈ =>
        simp only [n]
        rw [min_eq_right h₈]
        exact h₆
    replace h₇ : p ∣ n ^ 2 + 1 := by
      rw [Int.modEq_iff_dvd, sub_sub] at h₇
      apply dvd_sub (show (p : ℤ) ∣ p by rfl) at h₇
      rw [<-sub_add] at h₇
      simp at h₇
      norm_cast at h₇
      rw [add_comm] at h₇
      exact h₇
    have h₈ : n ≤ (p - 1) / 2 := by
      omega
    exact ⟨n, h₇, h₈⟩
  -- Show that for such primes p and n, p > 2n + √(10n).
  have h₂ (p n : ℕ) (hp₁ : Nat.Prime p) (hp₂ : p ≡ 1 [MOD 8]) (hn₁ : p ∣ n ^ 2 + 1) (hn₂ : n ≤ (p - 1) / 2) : p > 2 * n + Real.sqrt (2 * n) := by
    have hp₂' : ∃ k, p = 8 * k + 1 := by
      symm at hp₂
      rw [Nat.modEq_iff_dvd', dvd_iff_exists_eq_mul_right] at hp₂
      obtain ⟨k, hp₂⟩ := hp₂
      use k
      rw [<-hp₂, Nat.sub_add_cancel]
      all_goals
        linarith only [Nat.Prime.two_le hp₁]
    obtain ⟨k, hp₂'⟩ := hp₂'
    replace hp₁ : Nat.Prime p ∧ p ≥ 3 := by
      have h₂ : 2 ≤ p := Nat.Prime.two_le hp₁
      rw [hp₂'] at h₂
      refine ⟨hp₁, by omega⟩
    -- Let ℓ = (p - 1) / 2 - n.
    let ℓ := (p - 1) / 2 - n
    have h₂ : n = (p - 1) / 2 - ℓ := by
      simp [ℓ]
      rw [Nat.sub_sub_self (by omega)]
    replace hn₁ : n ^ 2 + 1 ≡ 0 [ZMOD p] := by
      rw [Int.modEq_iff_dvd]
      apply dvd_sub (by simp) (by norm_cast)
    -- Show that (2ℓ + 1)² + 4 ≡ 0 (mod p).
    have h₃ : (2 * ℓ + 1) ^ 2 + 4 ≡ 0 [ZMOD p] := by
      rw [h₂] at hn₁
      replace hn₁ := Int.ModEq.mul_left 4 hn₁
      rw [mul_add] at hn₁
      norm_cast at hn₁
      nth_rewrite 1 [show 4 = 2 ^ 2 by norm_num] at hn₁
      rw [<-mul_pow, Nat.mul_sub, Nat.mul_comm, Nat.div_mul_cancel (by rw [hp₂']; omega)] at hn₁
      ring_nf at hn₁
      refine Int.ModEq.trans ?_ hn₁
      simp
      rw [add_comm]
      apply Int.ModEq.add_left
      rw [<-neg_sq]
      apply Int.ModEq.pow
      rw [Int.modEq_iff_dvd, sub_neg_eq_add, Nat.sub_sub, Nat.add_comm, Nat.mul_comm]
      norm_cast
      rw [Nat.sub_add_cancel]
      omega
    -- The square of an odd number is always congruent to 1 modulo 8.
    have h₄ : (2 * ℓ + 1) ^ 2 ≡ 1 [MOD 8] := by
      by_cases h₄ : Odd ℓ
      . simp [Odd] at h₄
        obtain ⟨ℓ', h₄⟩ := h₄
        rw [h₄]
        ring_nf
        symm
        rw [Nat.modEq_iff_dvd']
        omega
        omega
      . simp [Even] at h₄
        obtain ⟨ℓ', h₄⟩ := h₄
        rw [h₄]
        ring_nf
        symm
        rw [Nat.modEq_iff_dvd']
        omega
        omega
    -- Let (2ℓ + 1)² + 4 = rp for some r.
    symm at h₃
    rw [Int.modEq_iff_dvd] at h₃
    simp at h₃
    norm_cast at h₃
    rw [dvd_iff_exists_eq_mul_left] at h₃
    obtain ⟨r, h₃⟩ := h₃
    replace h₄ := Nat.ModEq.add_right 4 h₄
    rw [h₃] at h₄
    replace h₄ : r * p ≡ 5 * p [MOD 8] := by
      refine Nat.ModEq.trans h₄ ?_
      rw [show 1 + 4 = 5 * 1 by norm_num]
      apply Nat.ModEq.mul_left
      exact hp₂.symm
    have hp₂'' : ¬p ∣ 8 := by
      by_contra!
      rw [show 8 = 2 ^ 3 by norm_num] at this
      apply Prime.dvd_of_dvd_pow at this
      apply Nat.le_of_dvd at this
      omega
      norm_num
      rw [<-Nat.prime_iff]
      exact hp₁.1
    replace h₄ := Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm, <-Nat.coprime_iff_gcd_eq_one, Nat.Prime.coprime_iff_not_dvd hp₁.1]; exact hp₂'') h₄
    -- Show that r ≥ 5.
    have h₅ : r ≥ 5 := by
      symm at h₄
      rw [Nat.modEq_iff_dvd, dvd_iff_exists_eq_mul_left] at h₄
      obtain ⟨c, h₄⟩ := h₄
      omega
    replace h₃ : 2 * ℓ + 1 ≥ Real.sqrt (5 * p - 4) := by
      rw [ge_iff_le, Real.sqrt_le_left]
      norm_cast
      rw [Int.subNatNat_of_le (by omega)]
      norm_cast
      calc
        5 * p - 4 ≤ r * p - 4 := by apply Nat.sub_le_sub_right; apply Nat.mul_le_mul_right; apply h₅
        _ = (2 * ℓ + 1) ^ 2 + 4 - 4 := by rw [h₃]
      norm_cast
      omega
    norm_cast at h₃
    rw [Int.subNatNat_of_le (show 4 ≤ 5 * p by omega)] at h₃
    simp [ℓ] at h₃
    norm_cast at h₃
    rw [Nat.mul_sub] at h₃
    nth_rewrite 2 [Nat.mul_comm] at h₃
    rw [Nat.div_mul_cancel (by omega), Nat.sub_sub, Nat.add_comm 1 (2 * n), <-Nat.sub_sub, Nat.sub_add_cancel (by omega)] at h₃
    replace h₃ : p ≥ 2 * n + Real.sqrt (5 * p - 4 : ℕ) := by
      calc
        (p : ℝ) = p - 2 * n + 2 * n := by norm_cast; rw [Int.subNatNat_of_le (by omega)]; norm_cast; rw [Nat.sub_add_cancel (by omega)]
        _ ≥ 2 * n + Real.sqrt (5 * p - 4 : ℕ) := by norm_cast; rw [Int.subNatNat_of_le (by omega)]; zify; linarith only [h₃]
    calc
      (p : ℝ) ≥ 2 * n + Real.sqrt (5 * p - 4 : ℕ) := h₃
      _ > 2 * n + Real.sqrt (2 * n) := by
        apply add_lt_add_left
        apply Real.sqrt_lt_sqrt
        norm_cast
        omega
        norm_cast
        omega
  -- Show that there are infinitely many n such that n² + 1 has a prime divisor greater than 2n + √(2n).
  -- Assume for contradiction that there are only finitely many such n.
  by_contra! h₃
  rw [Set.not_infinite] at h₃
  let S := Set.Finite.toFinset h₃
  -- Show that S is non-empty by using (n, p) = (4, 17).
  have hS₀ : S.Nonempty := by
    simp [S, Set.Nonempty]
    use 4
    simp
    use 17
    exact ⟨by native_decide, by rfl, by simp; linarith only [show Real.sqrt 2 * Real.sqrt 4 < 9 by rw [<-Real.sqrt_mul, Real.sqrt_lt]; all_goals norm_num]⟩
  let N := S.max' hS₀
  -- Consider a prime p > N² + 1 such that p ≡ 1 (mod 8).
  obtain ⟨p, ⟨hp₀, hp₁⟩, hp₂⟩ := h₀.exists_gt (N ^ 2 + 1)
  -- Obtain n such that p | n² + 1 and n ≤ (p - 1) / 2.
  obtain ⟨n, hn₁, hn₂⟩ := h₁ p hp₀ hp₁
  -- Show that n > N, leading to a contradiction.
  have hn₃ : n > N := by
    by_contra! hn₃
    have hn₄ : N ^ 2 + 1 < N ^ 2 + 1 := by
      calc
        N ^ 2 + 1 < p := hp₂
        _ ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hn₁
        _ ≤ N ^ 2 + 1 := by simp; apply Nat.pow_le_pow_of_le_left hn₃
    linarith only [hn₄]
  -- Show that p > 2n + √(2n), leading to a contradiction.
  have hn₄ : p > 2 * n + Real.sqrt (2 * n) := h₂ p n hp₀ hp₁ hn₁ hn₂
  have hn₅ : n ∈ S := by
    simp [S]
    rw [gt_iff_lt] at hn₄
    simp at hn₄
    refine ⟨by omega, ⟨p, hp₀, ⟨hn₁, hn₄⟩⟩⟩
  have hn₆ : n ≤ N := by
    exact Finset.le_max' S n hn₅
  linarith only [hn₃, hn₆]
