import Mathlib

--set_option maxRecDepth 4000
set_option maxHeartbeats 800000

/- # Problem:
 Example 5 Given a positive integer $n$ that satisfies the following condition: In any $n$ integers greater than 1 and not exceeding 2009 that are pairwise coprime, at least one is a prime number. Find the minimum value of $n$. ${ }^{[2]}$
Since $44 < \sqrt{2009} < 45$, any composite number greater than 1 and not exceeding 2009 must have a a factor not exceeding 44. There are 14 prime numbers not exceeding 44, as follows: $2,3,5,7,11,13,17$, $19,23,29,31,37,41,43$. On one hand, $2^{2}, 3^{2}, 5^{2}, 7^{2}, 11^{2}, 13^{2}, 17^{2}$, $19^{2}, 23^{2}, 29^{2}, 31^{2}, 37^{2}, 41^{2}, 43^{2}$

are 14 positive integers greater than 1 and not exceeding 2009 that are pairwise coprime, and none of them are prime. Therefore, $n \geqslant 15$. On the other hand, let $a_{1}, a_{2}, \cdots, a_{15}$ be 15 positive integers greater than 1 and not exceeding 2009 that are pairwise coprime.

If they are all composite, let $p_{i}$ be the prime factor of $a_{i}$ not exceeding 44 $(i=1,2, \cdots, 15)$.

By the pigeonhole principle, there exist $i, j (1 \leqslant i < j \leqslant 15)$ such that $p_{i}=p_{j}$. Thus, $a_{i}$ and $a_{j}$ are not coprime, which is a contradiction. Therefore, among $a_{1}, a_{2}, \cdots, a_{15}$, there exists a prime number. In conclusion, the minimum value of $n$ is 15. -/
namespace number_theory_324136

theorem number_theory_324136 :
    IsLeast {n > 0 | (s : Finset ℕ) → s.card = n → (∀ x ∈ s, x > 1 ∧ x ≤ 2009) → (s : Set ℕ).Pairwise Nat.Coprime → ∃ p ∈ s, Nat.Prime p} 15 := by
  -- Since $44 < \sqrt{2009} < 45$, any composite number greater than 1 and not exceeding 2009 must have a prime factor not exceeding 44. There are 14 prime numbers not exceeding 44, as follows: $2,3,5,7,11,13,17$, $19,23,29,31,37,41,43$.
  have minfac_le_44_of_composite_in_bound : ∀ x, ¬ Nat.Prime x → x > 1 ∧ x ≤ 2009 → x.minFac ≤ 44 := by
    intro x x_not_prime x_bound
    rcases x_bound with ⟨x_gt_1, x_le_2009⟩
    have := Nat.minFac_sq_le_self (by linarith) x_not_prime
    have : x.minFac ≤ x.sqrt := by
      exact Nat.le_sqrt'.mpr this
    have : x.sqrt ≤ 44 := by
      have : x.sqrt ≤ (2009 : ℕ).sqrt := by
        exact Nat.sqrt_le_sqrt x_le_2009
      convert this
      . native_decide
    linarith
  let primes_le_44 := (Finset.Icc 2 44).filter Nat.Prime
  have primes_le_44_card_eq_14 : primes_le_44.card = 14 := by
    rfl
  constructor
  swap
  . simp [lowerBounds]
    intro n n_pos ex_prime
    by_contra
    have n_le_14 : n ≤ 14 := by
      linarith
    /-
    On one hand, $2^{2}, 3^{2}, 5^{2}, 7^{2}, 11^{2}, 13^{2}, 17^{2}$, $19^{2}, 23^{2}, 29^{2}, 31^{2}, 37^{2}, 41^{2}, 43^{2}$

    are 14 positive integers greater than 1 and not exceeding 2009 that are pairwise coprime, and none of them are prime. Therefore, $n \geqslant 15$.
     -/
    let s : Finset ℕ := primes_le_44.map ⟨(. ^ 2), by simp [Function.Injective]⟩
    have s_card_eq_14 : s.card = 14 := by
      exact primes_le_44_card_eq_14
    have s_bound : ∀ x ∈ s, x > 1 ∧ x ≤ 2009 := by
      native_decide
    have s_pairwise_coprime : (s : Set ℕ).Pairwise Nat.Coprime := by
      native_decide
    have : ∃ t ⊆ s, t.card = n := by
      exact Finset.exists_subset_card_eq n_le_14
    rcases this with ⟨t, t_subset_s, t_card_eq_n⟩
    have t_bound : ∀ x ∈ t, x > 1 ∧ x ≤ 2009 := by
      exact fun x x_in_t ↦ s_bound x (t_subset_s x_in_t)
    have t_pairwise_coprime : (t : Set ℕ).Pairwise Nat.Coprime := by
      exact Set.Pairwise.mono t_subset_s s_pairwise_coprime
    have ex_prime_in_t := ex_prime t t_card_eq_n t_bound t_pairwise_coprime
    have not_ex_prime_in_s : ¬ ∃ p ∈ s, Nat.Prime p := by
      native_decide -- use `native_decide` instead of `decide` here to speed up
    have not_ex_prime_in_t : ¬ ∃ p ∈ t, Nat.Prime p := by
      rintro ⟨p, p_in_t, p_prime⟩
      have p_in_s : p ∈ s := by
        exact t_subset_s p_in_t
      exact not_ex_prime_in_s ⟨p, p_in_s, p_prime⟩
    exact not_ex_prime_in_t (ex_prime t t_card_eq_n t_bound t_pairwise_coprime)
  . -- On the other hand, let $a_{1}, a_{2}, \cdots, a_{15}$ be 15 positive integers greater than 1 and not exceeding 2009 that are pairwise coprime.
    simp
    intro s s_card s_bound s_pairwise_coprime
    -- If they are all composite, let $p_{i}$ be the prime factor of $a_{i}$ not exceeding 44 $(i=1,2, \cdots, 15)$.
    by_contra all_in_s_not_prime
    simp at all_in_s_not_prime
    --simp [Nat.Prime, Irreducible] at all_in_s_not_prime
    let ps := s.image Nat.minFac
    -- By the pigeonhole principle, there exist $i, j (1 \leqslant i < j \leqslant 15)$ such that $p_{i}=p_{j}$. Thus, $a_{i}$ and $a_{j}$ are not coprime, which is a contradiction. Therefore, among $a_{1}, a_{2}, \cdots, a_{15}$, there exists a prime number. In conclusion, the minimum value of $n$ is 15.
    have : ps ⊆ primes_le_44 := by
      simp [ps, primes_le_44]
      intro p p_in_ps
      simp at p_in_ps
      rcases p_in_ps with ⟨x, x_in_s, rfl⟩
      simp
      have prime_minFac : x.minFac.Prime := by
        refine Nat.minFac_prime ?_
        have := s_bound x x_in_s
        linarith
      constructor
      . constructor
        . exact prime_minFac.two_le
        . exact minfac_le_44_of_composite_in_bound x (all_in_s_not_prime x x_in_s) (s_bound x x_in_s)
      . exact prime_minFac
    have : ps.card < s.card := by
      have : ps.card ≤ primes_le_44.card := by
        exact Finset.card_mono this
      rw [primes_le_44_card_eq_14] at this
      linarith
    have not_injOn : ¬ Set.InjOn Nat.minFac s := by
      intro injOn
      have : ps.card = s.card := by
        exact Finset.card_image_iff.mpr injOn
      linarith
    unfold Set.InjOn at not_injOn
    norm_cast at not_injOn
    push_neg at not_injOn
    rcases not_injOn with ⟨p, p_in, q, q_in, p_minFac_eq_q_minFac, p_ne_q⟩
    have p_coprime_q := s_pairwise_coprime p_in q_in p_ne_q
    let minFac := p.minFac
    have : p.gcd q ≥ 2 := by
      suffices p.gcd q ≥ minFac by
        have : minFac ≥ 2 := by
          have : minFac.Prime := by
            refine Nat.minFac_prime ?_
            have := s_bound p p_in
            linarith
          exact this.two_le
        linarith
      suffices minFac ∣ p.gcd q by
        --refine Nat.minFac_le_of_dvd ?_ ?_
        apply Nat.le_of_dvd
        . -- Interesting, we can derive this from a contradicting hypothesis here and it's logically correct.
          exact Nat.lt_of_sub_eq_succ p_coprime_q
        . exact this
      have dvd_p : minFac ∣ p := by
        exact Nat.minFac_dvd p
      have dvd_q : minFac ∣ q := by
        unfold minFac
        rw [p_minFac_eq_q_minFac]
        exact Nat.minFac_dvd q
      exact Nat.dvd_gcd dvd_p dvd_q
    linarith

end number_theory_324136
open number_theory_324136
