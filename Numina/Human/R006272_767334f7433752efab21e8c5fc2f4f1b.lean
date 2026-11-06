import Mathlib


/- Let $k$ be a natural number such that $k \ge 1$. Let $p_1, p_2, \ldots, p_k$ be $k$ distinct prime numbers. Let $n$ be the product of these primes, i.e., $n = p_1 p_2 \cdots p_k$.
Suppose that for each $i \in \{1, 2, \ldots, k\}$, the term $p_i-1$ divides $n-1$.
Show that for any integer $a$, $a^n \equiv a \pmod n$. -/
theorem number_theory_635419 (k n : ℕ) (hk: k ≥ 1) (p : ℕ → ℕ)
  (pp : ∀ i ∈ Finset.range k, Nat.Prime (p i))
  (distinct_p: ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, p i = p j → i = j)
  (neq: n = ∏ i ∈ Finset.range k, p i)
  (hdvd : ∀ i, (p i - 1) ∣ (n - 1)):
  ∀(a:ℤ), a ^ n ≡ a [ZMOD n] := by

  -- k = 1, p0 = 2, trivial.
  by_cases hh: k = 1 ∧ p 0 = 2
  · intro a
    simp only [hh, Finset.range_one, Finset.prod_singleton] at neq
    rw [neq]
    mod_cases hmod: a % 2
    all_goals
      have := hmod.pow 2
      refine this.trans ?_
      simp [hmod.symm]

  have npos: 0 < n := by
    rw [neq]
    apply Finset.prod_pos
    intro i hi
    exact (pp i hi).pos

  -- otherwise, n is odd. suffices to consider natural number a.
  suffices h: ∀b:ℕ, b^n ≡ b [MOD n] by
    push_neg at hh
    obtain ⟨j, j_mem, hpj⟩: ∃ j ∈ Finset.range k, p j ≠ 2 := by
      by_cases keq: k = 1
      · use 0
        simp [keq, hh]
      · change 0 < k at hk
        have hk': 1 < k := by omega
        have h1 := distinct_p 0 (by simp [hk]) 1 (by simp [hk'])
        have h2: p 1 ≠ p 0 := by
          rintro h2
          simp [h2] at h1
        by_cases hp0: p 0 = 2
        · use 1
          rw [hp0] at h2
          simp [hk', h2]
        · use 0
          simp [hk, hp0]
    have h1 := (pp j j_mem).even_sub_one hpj
    have h2: Even (n - 1) := (hdvd j).even h1
    have h3: Odd n := by
      rw [← Nat.sub_add_cancel npos]
      exact Even.add_one h2
    intro a
    specialize h a.natAbs
    rw [← Int.natCast_modEq_iff] at h
    push_cast at h
    by_cases ha: a ≥ 0
    · rwa [abs_of_nonneg ha] at h
    · push_neg at ha
      rw [abs_of_neg ha, h3.neg_pow] at h
      simpa only [Int.neg_modEq_neg] using h

  -- use chinese remainder theorem, suffices to show b^n modeq b for any pi.
  suffices h: ∀b:ℕ, ∀i ∈ Finset.range k, b^n ≡ b [MOD p i] by
    intro b; specialize h b
    have h1: ∀i ∈ (Finset.range k).toList, b^n ≡ b [MOD p i] := by
      simp only [Finset.mem_toList]
      exact h
    have h2: n = ((Finset.range k).toList.map p).prod := by
      simp [neq]
    nth_rw 1 [h2, Nat.modEq_list_prod_iff']
    exact h1
    apply List.Nodup.pairwise_of_forall_ne ?_ ?_
    · exact Finset.nodup_toList (Finset.range k)
    · simp only [Finset.mem_toList]
      intro i hi j hj inej
      specialize distinct_p i hi j hj
      suffices p i ≠ p j by
        exact (Nat.coprime_primes (pp i hi) (pp j hj)).mpr this
      exact fun a => inej (distinct_p a)

  intro b i hi

  -- if pi divide b, trivial.
  by_cases bdvd: p i ∣ b
  · have h1: b^n ≡ 0 [MOD p i] := by
      refine Nat.modEq_zero_iff_dvd.mpr ?_
      refine dvd_pow bdvd npos.ne'
    have h2: b ≡ 0 [MOD p i] := by
      exact Nat.modEq_zero_iff_dvd.mpr bdvd
    exact h1.trans h2.symm

  -- otherwise, by Fermat little theorem, b^(pi-1) ≡ 1 (mod pi)
  have h1: b^(p i - 1) ≡ 1 [MOD p i] := by
    rw [← Nat.totient_prime (pp i hi)]
    apply Nat.ModEq.pow_totient
    apply Nat.Coprime.symm
    rwa [(pp i hi).coprime_iff_not_dvd]

  -- then b^(n-1) ≡ 1 (mod pi), since pi-1 divide n-1, and therefore b^n modeq b.
  have h2: b^(n-1) ≡ 1 [MOD p i] := by
    rcases (hdvd i) with ⟨m, hm⟩
    rw [hm, Nat.pow_mul]
    nth_rw 2 [show 1 = 1^m by simp]
    exact h1.pow m
  rw [← Nat.sub_add_cancel npos, pow_succ]
  nth_rw 3 [← one_mul b]
  exact h2.mul rfl