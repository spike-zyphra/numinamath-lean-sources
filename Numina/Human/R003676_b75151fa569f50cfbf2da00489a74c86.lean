import Mathlib
set_option maxHeartbeats 1000000

/- # Problem:
 20. Let $a, b, c, d$ be positive integers such that the least common multiple (L.C.M.) of any three of them is $3^{3} \times 7^{5}$. How many different sets of $(a, b, c, d)$ are possible if the order of the numbers is taken into consideration?
(2 marks)
已知 $a 、 b 、 c 、 d$ 爲正整數, 綶中任意三個數的最小公倍數 (L.C.M. ) 圴爲 $3^{3} \times 7^{5}$ 。若需考虑各數的先後次序, 問 $(a, b, c, d)$ 有多少組不同的可能値?
20. 11457
21. Note that each of $a, b, c, d$ is of the form $3^{m} 7^{n}$ where $m$ is one of $0,1,2,3$ and $n$ is one of 0 ,1 , $2,3,4,5$. Furthermore, at least two of the four $m$ 's are equal to 3 and at least two of the four $n$ 's are equal to 5 . We first count the number of ways of choosing the four $m$ 's. There are three possibilities:

- If all of them are 3 , there is 1 choice.
- If exactly three of them are 3 , there are 4 ways to choose the outlier and 3 ways to choose the value of the outlier (namely, 0,1 or 2 ), giving $4 \times 3=12$ choices.
- If exactly two of them are 3 , there are $C_{2}^{4}=6$ ways to locate the 3 's, then $3^{2}=9$ ways to choose the value of the other two $m$ 's, giving $6 \times 9=54$ choices. Hence there are $1+12+54=67$ ways to choose the values of the $m$ 's. Likewise, there are $1+4 \times 5+C_{2}^{4} \times 5^{2}=171$ ways to choose the values of the $n$ 's. It follows that the answer is $67 \times 171=11457$. -/

lemma n_factorization_3: (3 ^ 3 * 7 ^ 5).factorization 3 = 3 := by
  native_decide

lemma n_factorization_7: (3 ^ 3 * 7 ^ 5).factorization 7 = 5 := by
  native_decide

lemma factorization_3_3_eq_1 : Nat.factorization 3 3 = 1 := by
  norm_num

lemma factorization_3_7_eq_0 : Nat.factorization 3 7 = 0 := by
  norm_num

lemma factorization_7_3_eq_0 : Nat.factorization 7 3 = 0 := by
  norm_num

lemma factorization_7_7_eq_1 : Nat.factorization 7 7 = 1 := by
  norm_num

lemma primeFactors_3_7 : {3, 7} = (3 ^ 3 * 7 ^ 5).primeFactors := by native_decide


lemma factorization_subset_primeFactors {n : ℕ} {F : Finset ℕ} (hn : n > 0) (hnF : n.primeFactors ⊆ F) (hF : ∀ p ∈ F, p.Prime): ∏ p ∈ F, p ^ n.factorization p = n := by
  nth_rw 2 [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  symm
  apply Finset.prod_subset hnF
  intro p hp1 hp2
  suffices n.factorization p = 0 by rw [this]; norm_num
  apply Nat.factorization_eq_zero_of_not_dvd
  contrapose hp2
  simp at hp2 ⊢
  exact ⟨hF p hp1, hp2, by omega⟩


lemma factorization_prime_n_eq_zero {p n : ℕ} (hpn : n ≠ p) (hp : p.Prime) : (Nat.factorization p) n = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  by_cases hn1 : n = 1
  . rw [hn1]
    left
    norm_num
  . right; left
    by_contra h
    rw [Nat.dvd_prime hp] at h
    omega

lemma factorization_unique_3 {a b: ℕ} : Nat.factorization (3^a * 7^b) 3 = a := by
  rw [Nat.factorization_mul, Nat.factorization_pow]
  simp
  rw [factorization_3_3_eq_1, factorization_7_3_eq_0]
  all_goals norm_num

lemma factorization_unique_7 {a b: ℕ} : Nat.factorization (3^a * 7^b) 7 = b := by
  rw [Nat.factorization_mul, Nat.factorization_pow]
  simp
  rw [factorization_3_7_eq_0, factorization_7_7_eq_1]
  all_goals norm_num

-- Nat.lcm_eq_zero_iff does not exist in version 4.15, so we define a lemma
lemma nat_lcm_eq_zero_iff {m n : ℕ} : m.lcm n = 0 ↔ m = 0 ∨ n = 0 := by
  cases m <;> cases n <;> simp [Nat.lcm_ne_zero] at *

theorem number_theory_206127 :
  {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    (a.lcm b).lcm c = 3^3 * 7^5 ∧
    (a.lcm b).lcm d = 3^3 * 7^5 ∧
    (c.lcm d).lcm a = 3^3 * 7^5 ∧
    (c.lcm d).lcm b = 3^3 * 7^5}.ncard = 11457 := by

  let S := {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    (a.lcm b).lcm c = 3^3 * 7^5 ∧
    (a.lcm b).lcm d = 3^3 * 7^5 ∧
    (c.lcm d).lcm a = 3^3 * 7^5 ∧
    (c.lcm d).lcm b = 3^3 * 7^5}

  suffices S.ncard = 11457 by exact this
  let T1 := {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | max (max a b) c = 3 ∧ max (max a b) d = 3 ∧ max (max c d) a = 3 ∧ max (max c d) b = 3}
  let T2 := {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | max (max a b) c = 5 ∧ max (max a b) d = 5 ∧ max (max c d) a = 5 ∧ max (max c d) b = 5}

  have hT1_card : T1.ncard = 67 := by
    unfold T1
    have : {(a, b, c, d): ℕ × ℕ × ℕ × ℕ | a ⊔ b ⊔ c = 3 ∧ a ⊔ b ⊔ d = 3 ∧ c ⊔ d ⊔ a = 3 ∧ c ⊔ d ⊔ b = 3} = Finset.filter (fun (a,b,c,d) =>
      (a ⊔ b ⊔ c = 3 ∧ a ⊔ b ⊔ d = 3 ∧ c ⊔ d ⊔ a = 3 ∧ c ⊔ d ⊔ b = 3)) (Finset.Icc (0 : ℕ) 3 ×ˢ Finset.Icc (0 : ℕ) 3 ×ˢ Finset.Icc (0 : ℕ) 3 ×ˢ Finset.Icc (0 : ℕ) 3) := by
      ext ⟨a, b, c, d⟩
      simp
      omega
    rw [this, Set.ncard_coe_Finset]
    native_decide

  have hT2_card : T2.ncard = 171 := by
    unfold T2
    have : {(a, b, c, d): ℕ × ℕ × ℕ × ℕ | a ⊔ b ⊔ c = 5 ∧ a ⊔ b ⊔ d = 5 ∧ c ⊔ d ⊔ a = 5 ∧ c ⊔ d ⊔ b = 5} = Finset.filter (fun (a,b,c,d) =>
      (a ⊔ b ⊔ c = 5 ∧ a ⊔ b ⊔ d = 5 ∧ c ⊔ d ⊔ a = 5 ∧ c ⊔ d ⊔ b = 5)) (Finset.Icc (0 : ℕ) 5 ×ˢ Finset.Icc (0 : ℕ) 5 ×ˢ Finset.Icc (0 : ℕ) 5 ×ˢ Finset.Icc (0 : ℕ) 5) := by
      ext ⟨a, b, c, d⟩
      simp
      omega
    rw [this, Set.ncard_coe_Finset]
    native_decide

  let f : (x : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) → x ∈ T1 ×ˢ T2 → (ℕ × ℕ × ℕ × ℕ) := fun x hx => (3^x.1.1*7^x.2.1, 3^x.1.2.1*7^x.2.2.1, 3^x.1.2.2.1*7^x.2.2.2.1, 3^x.1.2.2.2*7^x.2.2.2.2)
  have h1 : ∀ (a : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) (ha : a ∈ T1 ×ˢ T2), f a ha ∈ S := by
    intro ⟨⟨a1, b1, c1, d1⟩, ⟨a2, b2, c2, d2⟩⟩ ha
    unfold f
    simp
    unfold S
    simp only [Set.mem_setOf_eq]
    unfold T1 T2 at ha
    simp at ha
    obtain ⟨⟨ha1, ha2,ha3,ha4⟩, ⟨ha5, ha6, ha7, ha8⟩⟩ := ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    . norm_num
    . norm_num
    . norm_num
    . norm_num
    . apply Nat.eq_of_factorization_eq
      . by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        rcases h with h | h
        . rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . norm_num at h
      . norm_num
      . intro p
        by_cases hp3 : p = 3
        . rw [hp3, n_factorization_3]
          repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
          repeat rw [Nat.factorization_mul, Finsupp.add_apply]
          repeat rw [Nat.factorization_pow]
          simp
          rw [factorization_3_3_eq_1, factorization_7_3_eq_0]
          norm_num
          exact ha1
          all_goals by_contra h; try norm_num at h
          rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . by_cases hp7 : p = 7
          . rw [hp7, n_factorization_7]
            repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_3_7_eq_0, factorization_7_7_eq_1]
            norm_num
            exact ha5
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h
          . repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_prime_n_eq_zero hp3 (by norm_num)]
            rw [factorization_prime_n_eq_zero hp7 (by norm_num)]
            norm_num
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h

    . apply Nat.eq_of_factorization_eq
      . by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        rcases h with h | h
        . rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . norm_num at h
      . norm_num
      . intro p
        by_cases hp3 : p = 3
        . rw [hp3, n_factorization_3]
          repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
          repeat rw [Nat.factorization_mul, Finsupp.add_apply]
          repeat rw [Nat.factorization_pow]
          simp
          rw [factorization_3_3_eq_1, factorization_7_3_eq_0]
          norm_num
          exact ha2
          all_goals by_contra h; try norm_num at h
          rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . by_cases hp7 : p = 7
          . rw [hp7, n_factorization_7]
            repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_3_7_eq_0, factorization_7_7_eq_1]
            norm_num
            exact ha6
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h
          . repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_prime_n_eq_zero hp3 (by norm_num)]
            rw [factorization_prime_n_eq_zero hp7 (by norm_num)]
            norm_num
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h

    . apply Nat.eq_of_factorization_eq
      . by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        rcases h with h | h
        . rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . norm_num at h
      . norm_num
      . intro p
        by_cases hp3 : p = 3
        . rw [hp3, n_factorization_3]
          repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
          repeat rw [Nat.factorization_mul, Finsupp.add_apply]
          repeat rw [Nat.factorization_pow]
          simp
          rw [factorization_3_3_eq_1, factorization_7_3_eq_0]
          norm_num
          exact ha3
          all_goals by_contra h; try norm_num at h
          rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . by_cases hp7 : p = 7
          . rw [hp7, n_factorization_7]
            repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_3_7_eq_0, factorization_7_7_eq_1]
            norm_num
            exact ha7
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h
          . repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_prime_n_eq_zero hp3 (by norm_num)]
            rw [factorization_prime_n_eq_zero hp7 (by norm_num)]
            norm_num
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h
    . apply Nat.eq_of_factorization_eq
      . by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        rcases h with h | h
        . rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . norm_num at h
      . norm_num
      . intro p
        by_cases hp3 : p = 3
        . rw [hp3, n_factorization_3]
          repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
          repeat rw [Nat.factorization_mul, Finsupp.add_apply]
          repeat rw [Nat.factorization_pow]
          simp
          rw [factorization_3_3_eq_1, factorization_7_3_eq_0]
          norm_num
          exact ha4
          all_goals by_contra h; try norm_num at h
          rw [nat_lcm_eq_zero_iff] at h
          rcases h with h | h
          . norm_num at h
          . norm_num at h
        . by_cases hp7 : p = 7
          . rw [hp7, n_factorization_7]
            repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_3_7_eq_0, factorization_7_7_eq_1]
            norm_num
            exact ha8
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h
          . repeat rw [Nat.factorization_lcm, Finsupp.sup_apply]
            repeat rw [Nat.factorization_mul, Finsupp.add_apply]
            repeat rw [Nat.factorization_pow]
            simp
            rw [factorization_prime_n_eq_zero hp3 (by norm_num)]
            rw [factorization_prime_n_eq_zero hp7 (by norm_num)]
            norm_num
            all_goals by_contra h; try norm_num at h
            rw [nat_lcm_eq_zero_iff] at h
            rcases h with h | h
            . norm_num at h
            . norm_num at h

  have h2 : ∀ (a b : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) (ha : a ∈ T1 ×ˢ T2) (hb : b ∈ T1 ×ˢ T2), f a ha = f b hb → a = b := by
    intro ⟨⟨a1, b1, c1, d1⟩, ⟨a2, b2, c2, d2⟩⟩ ⟨⟨a3, b3, c3, d3⟩, ⟨a4, b4, c4, d4⟩⟩ ha hb hx
    unfold f at hx
    simp at hx
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    have : a1 = a3 := by
      apply congrArg (fun x => x.factorization 3) at hx1
      rw [factorization_unique_3, factorization_unique_3] at hx1
      exact hx1
    have : a2 = a4 := by
      apply congrArg (fun x => x.factorization 7) at hx1
      rw [factorization_unique_7, factorization_unique_7] at hx1
      exact hx1
    have : b1 = b3 := by
      apply congrArg (fun x => x.factorization 3) at hx2
      rw [factorization_unique_3, factorization_unique_3] at hx2
      exact hx2
    have : b2 = b4 := by
      apply congrArg (fun x => x.factorization 7) at hx2
      rw [factorization_unique_7, factorization_unique_7] at hx2
      exact hx2
    have : c1 = c3 := by
      apply congrArg (fun x => x.factorization 3) at hx3
      rw [factorization_unique_3, factorization_unique_3] at hx3
      exact hx3
    have : c2 = c4 := by
      apply congrArg (fun x => x.factorization 7) at hx3
      rw [factorization_unique_7, factorization_unique_7] at hx3
      exact hx3
    have : d1 = d3 := by
      apply congrArg (fun x => x.factorization 3) at hx4
      rw [factorization_unique_3, factorization_unique_3] at hx4
      exact hx4
    have : d2 = d4 := by
      apply congrArg (fun x => x.factorization 7) at hx4
      rw [factorization_unique_7, factorization_unique_7] at hx4
      exact hx4

    subst a1 a2 b1 b2 c1 c2 d1 d2
    rfl


  have h3 : ∀ b ∈ S, ∃ (a : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) (ha : a ∈ T1 ×ˢ T2), f a ha = b := by
    intro ⟨a, b, c, d⟩ ht
    use ⟨⟨a.factorization 3, b.factorization 3, c.factorization 3, d.factorization 3⟩, ⟨a.factorization 7, b.factorization 7, c.factorization 7, d.factorization 7⟩⟩
    have ha : ((a.factorization 3, b.factorization 3, c.factorization 3, d.factorization 3), (a.factorization 7, b.factorization 7, c.factorization 7, d.factorization 7)) ∈ T1 ×ˢ T2 := by
      simp
      unfold T1 T2
      simp only [Set.mem_setOf_eq]
      unfold S at ht
      simp only [Set.mem_setOf_eq] at ht
      obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ := ht
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
      . apply congrArg (fun x => x.factorization 3) at ht5
        rw [n_factorization_3] at ht5
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht5
        exact ht5
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
      . apply congrArg (fun x => x.factorization 3) at ht6
        rw [n_factorization_3] at ht6
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht6
        exact ht6
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
      . apply congrArg (fun x => x.factorization 3) at ht7
        rw [n_factorization_3] at ht7
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht7
        exact ht7
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
      . apply congrArg (fun x => x.factorization 3) at ht8
        rw [n_factorization_3] at ht8
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht8
        exact ht8
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
      . apply congrArg (fun x => x.factorization 7) at ht5
        rw [n_factorization_7] at ht5
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht5
        exact ht5
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
      . apply congrArg (fun x => x.factorization 7) at ht6
        rw [n_factorization_7] at ht6
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht6
        exact ht6
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
      . apply congrArg (fun x => x.factorization 7) at ht7
        rw [n_factorization_7] at ht7
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht7
        exact ht7
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
      . apply congrArg (fun x => x.factorization 7) at ht8
        rw [n_factorization_7] at ht8
        repeat rw [Nat.factorization_lcm, Finsupp.sup_apply] at ht8
        exact ht8
        all_goals try omega
        by_contra h
        rw [nat_lcm_eq_zero_iff] at h
        omega
    use ha
    unfold f
    simp
    unfold S at ht
    simp only [Set.mem_setOf_eq] at ht
    obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ := ht
    have hap: a.primeFactors ⊆ {3, 7} := by
      rw [primeFactors_3_7, ← ht7]
      exact Nat.primeFactors_mono (Nat.dvd_lcm_right (c.lcm d) a) (by omega)
    have hbp: b.primeFactors ⊆ {3, 7} := by
      rw [primeFactors_3_7, ← ht8]
      exact Nat.primeFactors_mono (Nat.dvd_lcm_right (c.lcm d) b) (by omega)
    have hcp: c.primeFactors ⊆ {3, 7} := by
      rw [primeFactors_3_7, ← ht5]
      exact Nat.primeFactors_mono (Nat.dvd_lcm_right (a.lcm b) c) (by omega)
    have hdp: d.primeFactors ⊆ {3, 7} := by
      rw [primeFactors_3_7, ← ht6]
      exact Nat.primeFactors_mono (Nat.dvd_lcm_right (a.lcm b) d) (by omega)

    have hp37 : (∀ p ∈ ({3, 7}:Finset ℕ), Nat.Prime p) := by
      intro p hp
      simp at hp
      rcases hp with rfl | rfl
      . norm_num
      . norm_num
    refine ⟨?_, ?_, ?_, ?_⟩
    . have := factorization_subset_primeFactors ht1 hap hp37
      rw [Finset.prod_pair (by norm_num)] at this
      exact this
    . have := factorization_subset_primeFactors ht2 hbp hp37
      rw [Finset.prod_pair (by norm_num)] at this
      exact this
    . have := factorization_subset_primeFactors ht3 hcp hp37
      rw [Finset.prod_pair (by norm_num)] at this
      exact this
    . have := factorization_subset_primeFactors ht4 hdp hp37
      rw [Finset.prod_pair (by norm_num)] at this
      exact this

  rw [← Set.ncard_congr f h1 h2 h3]

  have h4 : (T1 ×ˢ T2).encard = 11457 := by
    have hT1_encard : T1.encard = 67 := by
      rw [Set.ncard_def, ENat.toNat_eq_iff (by norm_num)] at hT1_card
      rw [hT1_card]
      norm_cast

    have hT2_encard : T2.encard = 171 := by
      rw [Set.ncard_def, ENat.toNat_eq_iff (by norm_num)] at hT2_card
      rw [hT2_card]
      norm_cast

    have hT1_finite: T1.encard < ⊤ := by rw [hT1_encard]; decide
    have hT2_finite: T2.encard < ⊤ := by rw [hT2_encard]; decide
    simp at hT1_finite hT2_finite

    have h_TT_finite: (T1 ×ˢ T2).Finite := Set.Finite.prod hT1_finite hT2_finite
    rw [Set.Finite.encard_eq_coe_toFinset_card h_TT_finite]
    norm_cast
    rw [← Set.Finite.toFinset_prod, Finset.card_product]
    have : hT1_finite.toFinset.card = 67 := by
      rw [Set.Finite.encard_eq_coe_toFinset_card hT1_finite] at hT1_encard
      norm_cast at hT1_encard
    rw [this]
    have : hT2_finite.toFinset.card = 171 := by
      rw [Set.Finite.encard_eq_coe_toFinset_card hT2_finite] at hT2_encard
      norm_cast at hT2_encard
    rw [this]
  rw [Set.ncard_def, h4]
  norm_cast
