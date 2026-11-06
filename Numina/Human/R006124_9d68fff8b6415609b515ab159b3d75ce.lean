import Mathlib

/- # Problem:
 Determine the number of ordered triples $(a, b, c)$, where $a, b, c$ are positive integers, that satisfy the equation $(a^b)^c = 8^{6^7}$.
 1. We start with the equation $a^{bc} = 8^{6^7}$.
 2. Rewrite $8^{6^7}$ as a power of 2: $8^{6^7} = (2^3)^{6^7} = 2^{3 \cdot 6^7}$.
 3. Simplify the exponent: $2^{3 \cdot 6^7} = 2^{3 \cdot (2 \cdot 3)^7} = 2^{3 \cdot 2^7 \cdot 3^7} = 2^{3^8 \cdot 2^7}$.
 4. Thus, the equation becomes $a^{bc} = 2^{3^8 \cdot 2^7}$.
 5. For the equation to hold, $a$ must be a power of 2, say $a = 2^k$ for some positive integer $k$.
 6. Substituting $a = 2^k$ into the equation, we get $(2^k)^{bc} = 2^{3^8 \cdot 2^7}$, which simplifies to $2^{kbc} = 2^{3^8 \cdot 2^7}$.
 7. Equating the exponents, we have $kbc = 3^8 \cdot 2^7$.
 8. Since $k$ is a positive integer, $k$ must be a divisor of $3^8 \cdot 2^7$.
 9. Let $k = 2^m \cdot 3^n$ where $0 \leq m \leq 7$ and $0 \leq n \leq 8$.
10. Then, $bc = \frac{3^8 \cdot 2^7}{2^m \cdot 3^n} = 3^{8-n} \cdot 2^{7-m}$.
11. The number of ways to choose $b$ and $c$ such that $bc = 3^{8-n} \cdot 2^{7-m}$ is the number of divisors of $3^{8-n} \cdot 2^{7-m}$, which is $(8-n+1)(7-m+1) = (9-n)(8-m)$.
12. Summing over all possible values of $m$ and $n$, we get: \[ \sum_{m=0}^{7} \sum_{n=0}^{8} (9-n)(8-m) \]
13. This can be separated into two sums: \[ \sum_{m=0}^{7} (8-m) \sum_{n=0}^{8} (9-n) \]
14. Calculate the inner sums: \[ \sum_{m=0}^{7} (8-m) = 8 + 7 + 6 + 5 + 4 + 3 + 2 + 1 = 36 \] \[ \sum_{n=0}^{8} (9-n) = 9 + 8 + 7 + 6 + 5 + 4 + 3 + 2 + 1 = 45 \]
15. Multiply the results of the inner sums: \[ 36 \cdot 45 = 1620 \]
16. Therefore, the number of ordered triples $(a, b, c)$ is \\boxed{1620}. -/

lemma factorization_unique_2_3 {a b c d : ℕ} : 2^a * 3^b = 2^c * 3^d → a = c ∧ b = d := by
  intro h
  constructor
  . apply congrArg (fun x => x.factorization 2) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 2 = 1 by norm_num] at h
    rw [show (Nat.factorization 3) 2 = 0 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 3) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 3 = 0 by norm_num] at h
    rw [show (Nat.factorization 3) 3 = 1 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h



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

lemma factorization_subset_primeFactors_2 {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2} → 2 ^ n.factorization 2 = n := by
  intro h
  have hp : ∀ p ∈ ({2}: Finset ℕ), Nat.Prime p := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals norm_num
  have := factorization_subset_primeFactors hn h hp
  simp at this
  exact this

lemma factorization_subset_primeFactors_2_3 {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2, 3} → 2 ^ n.factorization 2 * 3 ^ n.factorization 3 = n := by
  intro h
  have hp : ∀ p ∈ ({2, 3}: Finset ℕ), Nat.Prime p := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals norm_num
  have := factorization_subset_primeFactors hn h hp
  rw [Finset.prod_pair (by norm_num)] at this
  exact this

theorem number_theory_618053 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ (a ^ b) ^ c = 8 ^ (6 ^ 7)}.encard = 1620 := by


  -- rw [show 8 ^ (6 ^ 7) = 2 ^ (3 ^ 8 * 2 ^ 7) by native_decide]
  let S := {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ (a ^ b) ^ c = 8 ^ (6 ^ 7)}
  let Tf := Finset.filter (fun ⟨a, b, c, a', b', c'⟩ =>
    (a + b + c = 7
    ∧ a' + b' + c' = 8))
    (Finset.Icc (0 : ℕ) 7 ×ˢ Finset.Icc (0 : ℕ) 7 ×ˢ Finset.Icc (0 : ℕ) 7 ×ˢ Finset.Icc (0 : ℕ) 8 ×ˢ Finset.Icc (0 : ℕ) 8 ×ˢ Finset.Icc (0 : ℕ) 8)

  let T := {(a, b, c, a', b', c') : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ | a + b + c = 7
    ∧ a' + b' + c' = 8
  }
  have h_T_eq_Tf: T = Tf := by
    unfold Tf T
    ext ⟨a, b, c, a', b', c'⟩
    simp
    omega

  have h_Tf_card: Tf.card = 1620 := by native_decide

  have h_T_card: T.encard = 1620 := by
    rw [h_T_eq_Tf, Set.encard_coe_eq_coe_finsetCard, h_Tf_card]
    norm_cast

  let f1 : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) := fun (a, b, c, a', b', c') => (2^(2^a * 3^a'), 2^b * 3^b', 2^c * 3^c')

  have hf1 : Set.InjOn f1 T := by
    unfold f1 T
    intro ⟨a, b, c, a', b', c'⟩ hx ⟨a1, b1, c1, a2, b2, c2⟩ hy hxy
    simp at hxy
    obtain ⟨hxy1, hxy2, hxy3⟩ := hxy
    apply factorization_unique_2_3 at hxy1
    apply factorization_unique_2_3 at hxy2
    apply factorization_unique_2_3 at hxy3
    obtain ⟨hxy11, hxy12⟩ := hxy1
    obtain ⟨hxy21, hxy22⟩ := hxy2
    obtain ⟨hxy31, hxy32⟩ := hxy3
    subst a a' b b' c c'
    rfl

  have h1 : f1 '' T = S := by
    unfold f1 S
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    . rintro ⟨⟨a, b, c, a', b', c'⟩, ⟨h1, h2⟩⟩
      simp at h1 h2
      rw [← h2]
      simp only
      refine ⟨?_, ?_, ?_, ?_⟩
      . simp
      . simp
      . simp
      . rw [← Nat.pow_mul]
        rw [← Nat.pow_mul]
        rw [show 8 ^ (6 ^ 7) = 2 ^ (3 ^ 8 * 2 ^ 7) by native_decide]
        rw [pow_right_inj₀ (by omega) (by omega)]
        rw [show 2 ^ a * 3 ^ a' * (2 ^ b * 3 ^ b' * (2 ^ c * 3 ^ c')) = 2 ^ (a + b + c) * 3 ^ (a' + b' + c') by ring]
        unfold T at h1
        simp at h1
        obtain ⟨h11, h12⟩ := h1
        rw [h11, h12]
        ring

    . intro ⟨h1, h2, h3, h⟩
      have : Nat.log 2 x.1 ≠ 0 := by
        by_contra hc
        simp at hc
        have : x.1 = 1 := by omega
        rw [this] at h
        simp only [one_pow] at h
        norm_num at h

      have : x.2.1 ≠ 0 := by
        by_contra hc
        rw [hc] at h
        simp only [pow_zero, one_pow] at h
        norm_num at h
        
      have : x.2.2 ≠ 0 := by
        by_contra hc
        rw [hc] at h
        simp only [pow_zero, one_pow] at h
        norm_num at h

      have : Nat.log 2 x.1 * x.2.1 ≠ 0 := by
        by_contra hc
        simp at hc
        rcases hc with hc1 | hc2
        . have : x.1 = 1 := by omega
          rw [this] at h
          simp only [one_pow] at h
          norm_num at h
        . omega

      have h_x1 : x.1 = 2 ^ (Nat.log 2 x.1) := by
        rw [← Nat.pow_mul] at h
        rw [show 8 ^ (6 ^ 7) = 2 ^ (3 ^ 8 * 2 ^ 7) by native_decide] at h
        have : 2 ^ x.1.factorization 2 = x.1 := by
          apply factorization_subset_primeFactors_2 (by omega)
          intro y hy
          simp at hy
          simp
          obtain ⟨hy1, hy2, hy3⟩ := hy
          have h4: y ∣ x.1 ^ (x.2.1 * x.2.2) := by
            apply dvd_pow
            . exact hy2
            . by_contra hc
              simp at hc
              rcases hc with hc1 | hc2
              all_goals omega

          rw [h] at h4
          exact @Nat.prime_eq_prime_of_dvd_pow (3 ^ 8 * 2 ^ 7) y 2 hy1 (by norm_num) h4

        nth_rw 2 [← this]
        rw [Nat.log_pow (by norm_num)]
        exact this.symm

      rw [← Nat.pow_mul] at h
      rw [h_x1] at h
      rw [← Nat.pow_mul] at h
      rw [show 8 ^ 6 ^ 7 = 2 ^ (3 ^ 8 * 2 ^ 7) by native_decide] at h
      rw [pow_right_inj₀ (by omega) (by omega)] at h
      rw [← mul_assoc] at h

      unfold T
      simp
      use (Nat.log 2 x.1).factorization 2
      use x.2.1.factorization 2
      use x.2.2.factorization 2
      use (Nat.log 2 x.1).factorization 3
      use x.2.1.factorization 3
      use x.2.2.factorization 3
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . apply congrArg (fun x => x.factorization 2) at h
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
        repeat rw [Nat.factorization_pow] at h
        simp at h
        rw [show (Nat.factorization 3) 2 = 0 by norm_num] at h
        rw [show (Nat.factorization 2) 2 = 1 by norm_num] at h
        simp at h
        exact h
        . norm_num
        . norm_num
        all_goals assumption
      . apply congrArg (fun x => x.factorization 3) at h
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
        repeat rw [Nat.factorization_pow] at h
        simp at h
        rw [show (Nat.factorization 3) 3 = 1 by norm_num] at h
        rw [show (Nat.factorization 2) 3 = 0 by norm_num] at h
        simp at h
        exact h
        . norm_num
        . norm_num
        all_goals assumption
      . apply Prod.ext
        . simp
          nth_rw 3 [h_x1]
          rw [pow_right_inj₀ (by omega) (by omega)]
          apply factorization_subset_primeFactors_2_3 (by omega)
          have : (Nat.log 2 x.1) ∣ 3 ^ 8 * 2 ^ 7 := by
            rw [← h]
            use x.2.1 * x.2.2
            ring
          have := Nat.primeFactors_mono this (by norm_num)
          rw [show Nat.primeFactors (3 ^ 8 * 2 ^ 7) = {2, 3} by native_decide] at this
          exact this

        . apply Prod.ext
          . simp
            apply factorization_subset_primeFactors_2_3 (by omega)
            have : x.2.1 ∣ 3 ^ 8 * 2 ^ 7 := by
              rw [← h]
              use Nat.log 2 x.1 * x.2.2
              ring

            have := Nat.primeFactors_mono this (by norm_num)
            rw [show Nat.primeFactors (3 ^ 8 * 2 ^ 7) = {2, 3} by native_decide] at this
            exact this

          . simp
            apply factorization_subset_primeFactors_2_3 (by omega)
            have : x.2.2 ∣ 3 ^ 8 * 2 ^ 7 := by
              rw [← h]
              use Nat.log 2 x.1 * x.2.1
              ring
            have := Nat.primeFactors_mono this (by norm_num)
            rw [show Nat.primeFactors (3 ^ 8 * 2 ^ 7) = {2, 3} by native_decide] at this
            exact this

  have h3 := Set.InjOn.encard_image hf1
  rw [h1, h_T_card] at h3
  exact h3
