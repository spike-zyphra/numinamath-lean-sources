import Mathlib

/- # Problem:
 1. Determine the smallest natural number whose half is a perfect square, a third is a perfect cube, and a fifth is a perfect fifth power.
Решение. Бараниот број мора да е делив со 2,3 и 5 (од условот), па мора да е од облик $n=2^{x} 3^{y} 5^{z}$. Ако има други множители нема да биде најмал. Од условот на задачата имаме: $\frac{n}{2}=2^{x-1} 3^{y} 5^{Z}$ (1) $\frac{n}{3}=2^{x} 3^{y-1} 5^{z}$ $\frac{n}{5}=2^{x} 3^{y} 5^{z-1}$

Од (1) следи дека $x-1, y, z$ мора да се парни. Од (2) следи дека $x, y-1, z$ мора да се деливи со три. Од (3) следи дека $x, y, z-1$ мора да се деливи со пет.

Значи $x$ е непарен, делив со 3 и со $5, y$ е парен, делив со 5 и дава остаток 1 при делење со $3, z$ е парен, делив со 3 и дава остаток 1 при делење со 5. Бидејќи $\mathbf{n}$ е најмал, тогаш и $x, y$ и $z$ мора да се најмали, па имаме $x=15, y=15, z=6$.

Значи $n=2^{15} 3^{10} 5^{6}=30233088000000$. -/

theorem number_theory_223203 : IsLeast {n | 0 < n ∧ ∃ k, n = 2 * k ^ 2 ∧ ∃ m, n = 3 * m ^ 3 ∧ ∃ p, n = 5 * p ^ 5} (2 ^ 15 * 3 ^ 10 * 5 ^ 6) := by
  constructor
  . simp only [Set.mem_setOf_eq]
    refine ⟨by simp, ?_⟩
    use 2 ^ 7 * 3 ^ 5 * 5 ^ 3
    refine ⟨by simp, ?_⟩
    use 2 ^ 5 * 3 ^ 3 * 5 ^ 2
    refine ⟨by simp, ?_⟩
    use 2 ^ 3 * 3 ^ 2 * 5
    simp

  . unfold lowerBounds
    simp only [Set.mem_setOf_eq]
    rintro n ⟨hn_pos, k, hk, m, hm, p, hp⟩

    have hn_ne_zero : n ≠ 0 := by omega

    have hm_ne_zero : m ^ 3 ≠ 0 := by
      by_contra h
      rw [h] at hm
      norm_num at hm
      contradiction
    have hp_ne_zero : p ^ 5 ≠ 0 := by
      by_contra h
      rw [h] at hp
      norm_num at hp
      contradiction
    have hk_ne_zero : k ^ 2 ≠ 0 := by
      by_contra h
      rw [h] at hk
      norm_num at hk
      contradiction

    have hn := Nat.factorization_prod_pow_eq_self hn_ne_zero
    rw [Nat.prod_factorization_eq_prod_primeFactors] at hn

    have h1 : {2, 3, 5} ⊆ n.primeFactors := by
      intro x hx
      simp at hx
      rcases hx with (rfl | rfl | rfl)
      all_goals simp
      all_goals refine ⟨?_, ?_, ?_⟩
      all_goals try norm_num
      all_goals try omega

    have hf : ∀ x ∈ n.primeFactors, x ∉ ({2,3,5}: Finset ℕ) → 1 ≤ x ^ n.factorization x := by
      intro x hx1 hx2
      rw [show 1 = x ^ 0 by norm_num]
      apply Nat.pow_le_pow_right
      . simp at hx1
        have := hx1.1
        by_contra h
        simp at h
        rw [h] at this
        norm_num at this
      . omega

    have h2 := Finset.prod_le_prod_of_subset_of_one_le' h1 hf
    rw [hn] at h2

    rw [Finset.prod_insert (by norm_num)] at h2
    rw [Finset.prod_pair (by norm_num)] at h2

    have hn1 : 15 ≤ n.factorization 2 := by
      have h1 : 3 ∣ n.factorization 2 := by
        apply congrArg (fun x => x.factorization 2) at hm
        rw [Nat.factorization_mul, Finsupp.add_apply] at hm
        rw [show (Nat.factorization 3) 2 = 0 by norm_num] at hm
        rw [Nat.factorization_pow] at hm
        simp at hm
        use m.factorization 2
        all_goals omega

      have h2 : 5 ∣ n.factorization 2 := by
        apply congrArg (fun x => x.factorization 2) at hp
        rw [Nat.factorization_mul, Finsupp.add_apply] at hp
        rw [show (Nat.factorization 5) 2 = 0 by norm_num] at hp
        rw [Nat.factorization_pow] at hp
        simp at hp
        use p.factorization 2
        all_goals omega
      have h3 : 0 < n.factorization 2 := by
        apply congrArg (fun x => x.factorization 2) at hk
        rw [hk, Nat.factorization_mul, Finsupp.add_apply]
        rw [show (Nat.factorization 2) 2 = 1 by norm_num]
        all_goals omega

      have h4 : 15 ∣ n.factorization 2 := by omega
      exact Nat.le_of_dvd h3 h4

    have hn2 : 10 ≤ n.factorization 3 := by
      have h1 : 2 ∣ n.factorization 3 := by
        apply congrArg (fun x => x.factorization 3) at hk
        rw [Nat.factorization_mul, Finsupp.add_apply] at hk
        rw [show (Nat.factorization 2) 3 = 0 by norm_num] at hk
        rw [Nat.factorization_pow] at hk
        simp at hk
        use k.factorization 3
        all_goals omega
      have h2 : 5 ∣ n.factorization 3 := by
        apply congrArg (fun x => x.factorization 3) at hp
        rw [Nat.factorization_mul, Finsupp.add_apply] at hp
        rw [show (Nat.factorization 5) 3 = 0 by norm_num] at hp
        rw [Nat.factorization_pow] at hp
        simp at hp
        use p.factorization 3
        all_goals omega
      have h3 : 0 < n.factorization 3 := by
        apply congrArg (fun x => x.factorization 3) at hm
        rw [hm, Nat.factorization_mul, Finsupp.add_apply]
        rw [show (Nat.factorization 3) 3 = 1 by norm_num]
        all_goals omega
      have h4 : 10 ∣ n.factorization 3 := by omega
      exact Nat.le_of_dvd h3 h4

    have hn3 : 6 ≤ n.factorization 5 := by
      have h1 : 2 ∣ n.factorization 5 := by
        apply congrArg (fun x => x.factorization 5) at hk
        rw [Nat.factorization_mul, Finsupp.add_apply] at hk
        rw [show (Nat.factorization 2) 5 = 0 by norm_num] at hk
        rw [Nat.factorization_pow] at hk
        simp at hk
        use k.factorization 5
        all_goals omega
      have h2 : 3 ∣ n.factorization 5 := by
        apply congrArg (fun x => x.factorization 5) at hm
        rw [Nat.factorization_mul, Finsupp.add_apply] at hm
        rw [show (Nat.factorization 3) 5 = 0 by norm_num] at hm
        rw [Nat.factorization_pow] at hm
        simp at hm
        use m.factorization 5
        all_goals omega
      have h3 : 0 < n.factorization 5 := by
        apply congrArg (fun x => x.factorization 5) at hp
        rw [hp, Nat.factorization_mul, Finsupp.add_apply]
        rw [show (Nat.factorization 5) 5 = 1 by norm_num]
        all_goals omega
      have h4 : 6 ∣ n.factorization 5 := by omega
      exact Nat.le_of_dvd h3 h4

    replace hn1 : 2 ^ 15 ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) hn1
    replace hn2 : 3 ^ 10 ≤ 3 ^ n.factorization 3 := Nat.pow_le_pow_right (by norm_num) hn2
    replace hn3 : 5 ^ 6 ≤ 5 ^ n.factorization 5 := Nat.pow_le_pow_right (by norm_num) hn3

    have : (3 ^ 10 * 5 ^ 6) ≤ 3 ^ n.factorization 3 * 5 ^ n.factorization 5 := by
      apply Nat.mul_le_mul
      . exact hn2
      . exact hn3

    have : 2 ^ 15 * (3 ^ 10 * 5 ^ 6) ≤ 2 ^ n.factorization 2 * (3 ^ n.factorization 3 * 5 ^ n.factorization 5) := by
      apply Nat.mul_le_mul
      . exact hn1
      . exact this

    nth_rw 1 [← mul_assoc] at this
    exact Nat.le_trans this h2
