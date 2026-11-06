import Mathlib


-- 21. Given a positive integer $n$ that is a multiple of 5, and the least common multiple of $n$ and 5! is 5 times the greatest common divisor of $n$ and 10!. Then the number of $n$ that satisfies the condition is ( ).
-- (A) 12
-- (B) 24
-- (C) 36
-- (D) 48
-- (E) 72

-- 21. D.

-- 由题意, 知 $[n, 5!]=5(n, 10!)$, 即 $\left[5 \times 2^{3} \times 3, n\right]=5\left(2^{8} \times 3^{4} \times 5^{2} \times 7, n\right)$. 于是, $n$ 的素因数为 $2 、 3 、 5 、 7$. 设 $n=2^{\alpha} 3^{\beta} 5^{\gamma} 7^{\tau}$, 其中, $\alpha \in\{3,4, \cdots, 8\}$, $\beta \in\{1,2,3,4\}, \gamma \in\{3\}, \tau \in\{0,1\}$. 故所求 $n$ 的个数为 $6 \times 4 \times 1 \times 2=48$.
lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl

lemma factor_integer_factorial_5 : Nat.factorial 5 = 2 ^ 3 * 3 * 5 := by decide
lemma factor_integer_factorial_10 : Nat.factorial 10 = 2 ^ 8 * 3 ^ 4 * 5 ^ 2 * 7 := by decide

theorem number_theory_121842 :
  Set.ncard {n : ℕ | n > 0 ∧ 5 ∣ n ∧ n.lcm (Nat.factorial 5) = 5 * n.gcd (Nat.factorial 10)} = 48 := by


  let S1 := {n : ℕ | n > 0 ∧ 5 ∣ n ∧ n.lcm (Nat.factorial 5) = 5 * n.gcd (Nat.factorial 10)}
  let S2 : Set (ℕ × ℕ × ℕ) := (Finset.Icc 3 8) ×ˢ (Finset.Icc 1 4) ×ˢ (Finset.Icc 0 1)

  have h_S2_card: S2.ncard = 48 := by
    rw [Set.ncard_eq_toFinset_card']
    native_decide

  have h_S1_card: S2.ncard = S1.ncard := by
    let f : (x : ℕ × ℕ × ℕ) → x ∈ S2 → ℕ :=
      fun ⟨α, β, τ⟩ _ => (2 : ℕ) ^ α * (3 : ℕ) ^ β * (5 : ℕ) ^ 3 * (7 : ℕ) ^ τ

    apply Set.ncard_congr f
    . intro ⟨n2, n3, n7⟩ hn
      unfold f S1
      simp
      constructor
      . use 2 ^ n2 * 3 ^ n3 * 25 * 7 ^ n7; ring
      . unfold S2 at hn
        simp at hn
        have ⟨⟨hn1, hn2⟩, hn3, hn4, hn5⟩ := hn
        interval_cases n2
        all_goals interval_cases n3
        all_goals interval_cases n7
        all_goals native_decide

    . intro ⟨n2, n3, n7⟩ ⟨m2, m3, m7⟩ hn hm hf
      unfold f at hf
      simp at hf
      have h1 : n2 = m2 := by
        have := congr_arg (fun x => x.factorization 2) hf
        simp [
          show Nat.Prime 2 by norm_num,
          show Nat.Prime 3 by norm_num,
          show Nat.Prime 5 by norm_num,
          show Nat.Prime 7 by norm_num
        ] at this
        exact this
      have h2 : n3 = m3 := by
        have := congr_arg (fun x => x.factorization 3) hf
        simp [
          show Nat.Prime 2 by norm_num,
          show Nat.Prime 3 by norm_num,
          show Nat.Prime 5 by norm_num,
          show Nat.Prime 7 by norm_num
        ] at this
        exact this
      have h3 : n7 = m7 := by
        have := congr_arg (fun x => x.factorization 7) hf
        simp [
          show Nat.Prime 2 by norm_num,
          show Nat.Prime 3 by norm_num,
          show Nat.Prime 5 by norm_num,
          show Nat.Prime 7 by norm_num
        ] at this
        exact this
      rw [h1, h2, h3]

    . intro n hn
      unfold S1 at hn
      simp at hn
      obtain ⟨hn1, hn2, hn3⟩ := hn
      rw [factor_integer_factorial_5, factor_integer_factorial_10] at hn3
      unfold f
      simp
      use n.factorization 2, n.factorization 3, n.factorization 7
      constructor
      . unfold S2
        simp

        have ⟨hnf2a, hnf2b⟩ : 3 ≤ n.factorization 2 ∧ n.factorization 2 ≤ 8 := by
          have := congr_arg (fun x => x.factorization 2) hn3
          simp only [
            show Nat.Prime 2 by norm_num,
            show Nat.Prime 3 by norm_num,
            show Nat.Prime 5 by norm_num,
            show Nat.Prime 7 by norm_num
          ] at this
          rw [Nat.factorization_mul, Finsupp.add_apply] at this
          rw [show (Nat.factorization 5) 2 = 0 by norm_num] at this
          rw [Nat.factorization_gcd, Nat.factorization_lcm] at this
          rw [Finsupp.sup_apply, Finsupp.inf_apply] at this
          repeat rw [Nat.factorization_mul, Finsupp.add_apply] at this
          norm_num at this
          rw [show (Nat.factorization 8) 2 = 3 by native_decide] at this
          rw [show (Nat.factorization 256) 2 = 8 by native_decide] at this
          rw [show (Nat.factorization 81) 2 = 0 by native_decide] at this
          rw [show (Nat.factorization 25) 2 = 0 by native_decide] at this
          norm_num at this
          rw [max_def, min_def] at this
          split_ifs at this
          . rw [← this]; simp
          . norm_num at this
          all_goals norm_num
          all_goals try omega
          by_contra h_contra
          rw [Nat.gcd_eq_zero_iff] at h_contra
          norm_num at h_contra

        have ⟨hnf3a, hnf3b⟩ : 1 ≤ n.factorization 3 ∧ n.factorization 3 ≤ 4 := by
          have := congr_arg (fun x => x.factorization 3) hn3
          simp only [
            show Nat.Prime 2 by norm_num,
            show Nat.Prime 3 by norm_num,
            show Nat.Prime 5 by norm_num,
            show Nat.Prime 7 by norm_num
          ] at this
          rw [Nat.factorization_mul, Finsupp.add_apply] at this
          rw [show (Nat.factorization 5) 3 = 0 by norm_num] at this
          rw [Nat.factorization_gcd, Nat.factorization_lcm] at this
          rw [Finsupp.sup_apply, Finsupp.inf_apply] at this
          repeat rw [Nat.factorization_mul, Finsupp.add_apply] at this
          norm_num at this
          rw [show (Nat.factorization 8) 3 = 0 by native_decide] at this
          rw [show (Nat.factorization 256) 3 = 0 by native_decide] at this
          rw [show (Nat.factorization 81) 3 = 4 by native_decide] at this
          rw [show (Nat.factorization 25) 3 = 0 by native_decide] at this
          norm_num at this
          rw [max_def, min_def] at this
          split_ifs at this
          . rw [← this]; simp
          . norm_num at this
          . omega
          . rw [this]; simp
          all_goals norm_num
          all_goals try omega
          by_contra h_contra
          rw [Nat.gcd_eq_zero_iff] at h_contra
          norm_num at h_contra

        have hnf7 : n.factorization 7 ≤ 1 := by
          have := congr_arg (fun x => x.factorization 7) hn3
          simp only [
            show Nat.Prime 2 by norm_num,
            show Nat.Prime 3 by norm_num,
            show Nat.Prime 5 by norm_num,
            show Nat.Prime 7 by norm_num
          ] at this
          rw [Nat.factorization_lcm] at this
          nth_rw 2 [Nat.factorization_mul] at this
          rw [Finsupp.add_apply] at this
          rw [Nat.factorization_gcd] at this
          repeat rw [Nat.factorization_mul] at this
          norm_num at this
          rw [show (Nat.factorization 8) 7 = 0 by native_decide] at this
          rw [show (Nat.factorization 256) 7 = 0 by native_decide] at this
          rw [show (Nat.factorization 81) 7 = 0 by native_decide] at this
          rw [show (Nat.factorization 25) 7 = 0 by native_decide] at this
          norm_num at this
          exact this
          all_goals norm_num
          all_goals try omega
          by_contra h_contra
          rw [Nat.gcd_eq_zero_iff] at h_contra
          norm_num at h_contra

        refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
        all_goals assumption


      . have : n.factorization 5 = 3 := by
          have := congr_arg (fun x => x.factorization 5) hn3
          simp only [
            show Nat.Prime 2 by norm_num,
            show Nat.Prime 3 by norm_num,
            show Nat.Prime 5 by norm_num,
            show Nat.Prime 7 by norm_num
          ] at this
          rw [Nat.factorization_lcm] at this
          repeat rw [Nat.factorization_mul] at this
          rw [Nat.factorization_gcd] at this
          rw [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply] at this
          repeat rw [Nat.factorization_mul] at this
          norm_num at this
          rw [show (Nat.factorization 8) 5 = 0 by native_decide] at this
          rw [show (Nat.factorization 256) 5 = 0 by native_decide] at this
          rw [show (Nat.factorization 81) 5 = 0 by native_decide] at this
          rw [show (Nat.factorization 25) 5 = 2 by native_decide] at this
          norm_num at this
          rw [max_def, min_def] at this
          split_ifs at this
          . have : n.factorization 5 = 0 := by linarith
            rw [Nat.factorization_eq_zero_iff] at this
            contrapose this
            simp
            exact ⟨by norm_num, hn2, by omega⟩

          . norm_num at this
          . norm_num at this
          . rw [this]
          all_goals norm_num
          all_goals try omega
          by_contra h_contra
          rw [Nat.gcd_eq_zero_iff] at h_contra
          norm_num at h_contra


        rw [show 125 = 5 ^ (n.factorization 5) by rw [this]; norm_num]
        nth_rw 5 [factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
        have : n.primeFactors ⊆ {2, 3, 5, 7} := by
          intro p hp
          simp at hp
          obtain ⟨hp1, hp2, _⟩ := hp

          by_contra h_contra
          simp at h_contra
          obtain ⟨h_contra1, h_contra2, h_contra3, h_contra4⟩ := h_contra

          have := congr_arg (fun x => x.factorization p) hn3
          simp only [
            show Nat.Prime 2 by norm_num,
            show Nat.Prime 3 by norm_num,
            show Nat.Prime 5 by norm_num,
            show Nat.Prime 7 by norm_num,
            hp1
          ] at this
          rw [Nat.factorization_lcm] at this
          repeat rw [Nat.factorization_mul] at this
          rw [Nat.factorization_gcd] at this
          rw [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply] at this
          repeat rw [Nat.factorization_mul] at this
          norm_num at this
          rw [show (Nat.factorization 8) p = 0 by
            rw [Nat.factorization_eq_zero_of_not_dvd]
            by_contra h
            rw [(show 8 = 2 ^ 3 by norm_num), Nat.dvd_prime_pow (by norm_num)] at h
            obtain ⟨k, hk1, hk2⟩ := h
            interval_cases k
            all_goals contrapose hp1; rw [hk2]; norm_num
            rw [hk2] at h_contra1
            norm_num at h_contra1
          ] at this
          rw [show (Nat.factorization 256) p = 0 by
            rw [Nat.factorization_eq_zero_of_not_dvd]
            by_contra h
            rw [(show 256 = 2 ^ 8 by norm_num), Nat.dvd_prime_pow (by norm_num)] at h
            obtain ⟨k, hk1, hk2⟩ := h
            interval_cases k
            all_goals contrapose hp1; rw [hk2]; norm_num
            rw [hk2] at h_contra1
            norm_num at h_contra1
          ] at this
          rw [show (Nat.factorization 81) p = 0 by
            rw [Nat.factorization_eq_zero_of_not_dvd]
            by_contra h
            rw [(show 81 = 3 ^ 4 by norm_num), Nat.dvd_prime_pow (by norm_num)] at h
            obtain ⟨k, hk1, hk2⟩ := h
            interval_cases k
            all_goals contrapose hp1; rw [hk2]; norm_num
            rw [hk2] at h_contra2
            norm_num at h_contra2
          ] at this
          rw [show (Nat.factorization 25) p = 0 by
            rw [Nat.factorization_eq_zero_of_not_dvd]
            by_contra h
            rw [(show 25 = 5 ^ 2 by norm_num), Nat.dvd_prime_pow (by norm_num)] at h
            obtain ⟨k, hk1, hk2⟩ := h
            interval_cases k
            all_goals contrapose hp1; rw [hk2]; norm_num
            rw [hk2] at h_contra3
            norm_num at h_contra3
          ] at this
          repeat rw [Finsupp.single_apply] at this
          rw [max_def, min_def] at this
          split_ifs at this
          all_goals try omega
          . have : n.factorization p = 0 := by linarith
            rw [Nat.factorization_eq_zero_iff] at this
            contrapose this
            simp
            exact ⟨hp1, hp2, by omega⟩
          . by_contra h_contra
            rw [Nat.gcd_eq_zero_iff] at h_contra
            norm_num at h_contra


        have h_zero : ∀ p ∈ ({2, 3, 5, 7}: Finset ℕ), p ∉ n.primeFactors → p ^ n.factorization p = 1 := by
          intro p hp1 hp2
          suffices n.factorization p = 0 by
            rw [this]
            norm_num

          apply Nat.factorization_eq_zero_of_not_dvd
          contrapose hp2
          simp
          simp at hp2
          refine ⟨?_, hp2, by omega⟩
          simp at hp1
          rcases hp1 with rfl | rfl | rfl | rfl
          all_goals norm_num

        rw [Finset.prod_subset this h_zero]
        simp
        ring

  rw [← h_S2_card, h_S1_card]
