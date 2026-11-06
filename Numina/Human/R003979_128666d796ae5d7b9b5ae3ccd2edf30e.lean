import Mathlib

-- 7. (50 points) From the numbers 1 to 200, one or several were selected into a separate group with the following property: if there are at least two numbers in the group, then the sum of any two numbers in this group is divisible by 5. What is the maximum number of numbers that can be in a group with this property?
theorem number_theory_226605 : IsGreatest {Finset.card G | (G : Finset ℕ) (hG : G ⊆ Finset.Icc 1 200) (hG1 : ∀ m ∈ G, ∀ n ∈ G, m ≠ n → 5 ∣ m + n)} 40 := by
  -- Answer: 40.
  let G_dvd_5 := (Finset.Icc 1 200).filter (5 ∣ .)
  have G_dvd_5_card_eq_40 : G_dvd_5.card = 40 := by
    rfl
  constructor
  . simp
    use G_dvd_5
    simp [G_dvd_5, G_dvd_5_card_eq_40]
    . --intro m le_m m_le dvd_m n le_n n_le dvd_n
      omega
  . simp [upperBounds]
    intro card G dvd_sum_in_G G_subs card_eq
    subst card_eq
    -- Solution. Assume that a number $A$ was selected for the group such that its remainder when divided by 5 is $i \neq 0$. If there is another number $B$ in the group, then its remainder when divided by 5 must be $5-i$ so that $A+B$ is divisible by 5. We will show that there can be no other numbers in this group. Suppose there is another number $C$, and $j=C \bmod 5$. Then the numbers $i+j$ and $5-i+j$ are divisible by 5, as is their difference, which equals $2i-5$. This is impossible when $i \neq 0$.
    wlog card_gt_2 : G.card > 2
    . linarith
    have ex_3_distinct_in_G : ∃ m ∈ G, ∃ n ∈ G, ∃ k ∈ G, m ≠ n ∧ m ≠ k ∧ n ≠ k := by
      exact Finset.two_lt_card.mp card_gt_2
    rcases ex_3_distinct_in_G with ⟨m, m_in_G, ex_2_more_distinct_in_G⟩
    by_cases w_5_dvd_m : 5 ∣ m
    swap
    . rcases ex_2_more_distinct_in_G with ⟨n, n_in_G, k, k_in_G, m_ne_n, m_ne_k, n_ne_k⟩
      have := dvd_sum_in_G m m_in_G n n_in_G m_ne_n
      have := dvd_sum_in_G m m_in_G k k_in_G m_ne_k
      have : n % 5 = k % 5 := by
        omega
      have : n % 5 + k % 5 = 5 := by
        have := dvd_sum_in_G n n_in_G k k_in_G n_ne_k
        omega
      exfalso
      omega
    -- Now consider the alternative case where all numbers in the group are divisible by 5. Within the specified range, there are exactly 40 numbers that are multiples of 5, and all these numbers can simultaneously be included in the group.
    . have : G ⊆ G_dvd_5 := by
        intro n n_in_G
        simp [G_dvd_5]
        have : n ∈ Finset.Icc 1 200 := by
          exact G_subs n_in_G
        simp at this
        simp [this]
        by_cases w_m_eq_n : m = n
        . omega
        . specialize dvd_sum_in_G m m_in_G n n_in_G w_m_eq_n
          omega
      rw [←G_dvd_5_card_eq_40]
      exact Finset.card_le_card this
