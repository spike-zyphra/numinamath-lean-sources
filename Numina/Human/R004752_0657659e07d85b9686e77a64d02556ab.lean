import Mathlib
open Nat Real Finset Set
noncomputable section

/-8. There are $n$ integers, whose product is $n$, and whose sum is zero. Then $n$ ( ).
(A) must be even
(B) must be odd
(C) may be even or may be odd
(D) does not exist
Please retain the original text's line breaks and format, and output the translation result directly.-/
theorem number_theory_6011111:
  ∃ n : ℕ, (∃ a : Fin n → ℤ, (∏ i, a i) = n ∧ (∑ i, a i) = 0) ∧
  ∀ m : ℕ, (∃ a : Fin m → ℤ, (∏ i, a i) = m ∧ (∑ i, a i) = 0) → Even m := by
  -- Step $1$: Construct $n = 4$ with $a = [1, 2, -1, -2]$.
  let n := 4
  use n
  constructor
  -- Subgoal $1$: Show $∃ a : Fin 4 → ℤ$, product eq $4$, sum eq $0$.
  have h_n4_exists : ∃ a : Fin 4 → ℤ, (∏ i, a i) = n ∧ (∑ i, a i) = 0 := by
    let a : Fin 4 → ℤ := ![1, 2, -1, -2]
    use a
    constructor
    -- Subgoal $1.1$: Product eq $4$.
    have h_prod : ∏ i, a i = 4 := by rfl
    exact h_prod
    -- Subgoal $1.2$: Sum eq $0$.
    have h_sum : ∑ i, a i = 0 := by rfl
    exact h_sum
  exact h_n4_exists
  -- Step $2$: Prove $∀ m$, if $∃ a : Fin m → ℤ$, product eq $m$, sum eq $0$, then $m$ is even.
  have h_m_even : ∀ m : ℕ, (∃ a : Fin m → ℤ, (∏ i, a i) = m ∧ (∑ i, a i) = 0) → Even m := by
    intro m h_m_exists
    obtain ⟨a, h_prod, h_sum⟩ := h_m_exists
    by_contra h_m_odd
    -- Assume $m$ is odd, derive contradiction.
    have h_m_odd' : Odd m := by
      rwa [← Nat.not_even_iff_odd]
    have h_a_all_odd : ∀ i, Odd (a i) := by
      intro i
      have h_a_i_dvd_m : (a i).natAbs ∣ m := by
        have h_prod_nat : (∏ i, a i).natAbs = m := by
          rw [h_prod]
          simp [Int.natAbs_ofNat]
        have h_a_i_dvd_prod : (a i) ∣ ∏ i, a i := by
          exact Finset.dvd_prod_of_mem a (mem_univ i)
        have h_a_i_dvd_natAbs : (a i).natAbs ∣ (∏ i, a i).natAbs := by
          apply Int.natAbs_dvd_natAbs.mpr
          exact h_a_i_dvd_prod
        rwa [h_prod_nat] at h_a_i_dvd_natAbs
      have h_a_i_odd_nat : Odd (a i).natAbs := by
        apply Odd.of_dvd_nat h_m_odd' h_a_i_dvd_m
      have h_a_i_odd : Odd (a i) := by
        by_contra h_not_odd
        have h_even : Even (a i) := Int.not_odd_iff_even.mp h_not_odd
        have h_abs_even : Even (a i).natAbs := by
          rw [Int.natAbs_even]
          exact h_even
        have h_abs_odd : Odd (a i).natAbs := h_a_i_odd_nat
        have h_no_odd_even : ¬(Even (a i).natAbs ∧ Odd (a i).natAbs) := by norm_num
        have h_odd_even : (Even (a i).natAbs ∧ Odd (a i).natAbs) := by tauto
        contradiction
      exact h_a_i_odd
    have h_sum_odd : Odd (∑ i ∈  univ, a i) := by
      -- Define $m$ as $2k + 1$, prove for all $k$.
      have h_m_odd_eq : ∃ k, m = 2 * k + 1 := by
        cases h_m_odd' with | intro k hk =>
        use k
      obtain ⟨k, h_m_k⟩ := h_m_odd_eq
      suffices h_odd_for_odd_m : ∀ k, ∀ m : ℕ, m = 2 * k + 1 → ∀ a : Fin m → ℤ, (∀ i, Odd (a i)) → Odd (∑ i ∈ univ, a i) by
        exact h_odd_for_odd_m k m h_m_k a h_a_all_odd
      intro k
      induction k with
      | zero =>
        -- Base case: $k = 0$, $m = 2 * 0 + 1 = 1$.
        intro m h_m a h_a_odd
        have h_m_eq : m = 1 := by rw [h_m, mul_zero, zero_add]
        subst h_m_eq
        have h_sum_one : ∑ i ∈ univ, a i = a 0 := by
          have h_univ : (univ : Finset (Fin 1)) = {0} := by norm_num
          rw [h_univ, Finset.sum_singleton]
        rw [h_sum_one]
        exact h_a_odd 0
      | succ k ih =>
        -- Inductive step: $k → k + 1$, $m = 2 * k + 1 → m' = 2 * (k + 1) + 1 = 2 * k + 3$.
        intro m h_m a h_a_odd
        have h_m_eq : m = 2 * k + 3 := by
          rw [h_m, mul_succ]
        have h_card_odd : Odd (Finset.card (univ : Finset (Fin m))) := by
          rw [Finset.card_univ, h_m_eq]
          simp [Nat.odd_iff]
          omega
        have h_all_odd : ∀ i ∈ Finset.univ, Odd (a i) := by
          intro i _
          exact h_a_odd i
        -- Prove: odd number of odd integers sums to odd.
        have h_sum_odd_aux : Odd (∑ i ∈ univ, a i) := by
          cases h_card_odd with | intro k' hk' =>
            have h_card_eq : Finset.card univ = 2 * k' + 1 := hk'
            have h_sum_split : ∑ i ∈ univ, a i = ∑ i ∈ univ, (fun i => 2 * (a i / 2) + 1) i := by
              apply Finset.sum_congr rfl
              intro i _
              have h_odd : Odd (a i) := h_a_odd i
              cases h_odd with | intro k'' hk'' =>
                have h_div : a i = 2 * (a i / 2) + 1 := by
                  rw [hk'']
                  simp [Int.add_comm, Int.mul_comm]
                  have h_div_eq :  (k''* 2 + 1) / 2 = k'' := by omega
                  rw [add_comm, h_div_eq, mul_comm]
                rw [h_div]
            rw [h_sum_split]
            rw [Finset.sum_add_distrib]
            rw [Finset.sum_const]
            have h_smul : (univ : Finset (Fin m)).card • (1 : ℤ) = ↑((univ : Finset (Fin m)).card) := by
              simp [mul_one]
            rw [h_smul]
            have h_even_term : Even (2 * ∑ i ∈ (univ : Finset (Fin m)), a i / 2) := by norm_num
            have h_odd_term : Odd (2 * k' + 1) := by
              simp [Int.odd_iff]
            have h_odd_term : Odd (univ : Finset (Fin m)).card := by
              rw [h_card_eq]
              simp [Int.odd_iff]
            have h_odd_add : Odd (∑ x : Fin m, 2 * (a x / 2) + ↑((univ : Finset (Fin m)).card)) := by
              rw [add_comm]
              rw [← mul_sum]
              apply Odd.add_even
              exact_mod_cast h_odd_term
              exact h_even_term
            exact_mod_cast h_odd_add
        exact h_sum_odd_aux
    rw [h_sum] at h_sum_odd
    apply Int.not_odd_zero
    exact h_sum_odd
  exact h_m_even
