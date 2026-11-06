import Mathlib
open Nat Finset
set_option linter.unusedVariables false

/- Laat $m \geq 3$ en $n$ positieve gehele getallen zijn met $n>m(m-2)$. Vind het grootste positieve gehele getal $d$ zodat $d \mid n$ ! en $k \nmid d$ voor alle $k \in\{m, m+1, \ldots, n\}$. -/
theorem number_theory_605271 (m n : ℕ) (hm : 3 ≤ m) (hn : 0 < n)
    (hmn : n > m * (m - 2)) :
    IsGreatest {d | 0 < d ∧ d ∣ Nat.factorial n ∧ ∀ k ∈ Finset.Icc m n, ¬k ∣ d} (m - 1) := by 
    -- IsGreatest requires $m - 1$ to be in the set and the maximum element.
  rw [IsGreatest]
  constructor
  -- Part $1$: Prove $m - 1$ is in the set.
  · -- Prove $m - 1 > 0$.
    have h_m_minus_1_pos : m - 1 > 0 := by
      apply Nat.sub_pos_of_lt
      nlinarith
    -- Prove $m - 1 ∣ n!$.
    have h_m_minus_1_dvd_n_fact : m - 1 ∣ Nat.factorial n := by
      apply Nat.dvd_factorial
      · exact h_m_minus_1_pos
      · apply Nat.le_of_lt
        have : m - 2 ≥ 1 := by omega
        have : m * (m - 2) ≥ m := by nlinarith
        have : n > m - 1 := by omega
        exact this
    -- Prove $∀ k ∈ [m, n]$, $k ∤ m - 1$.
    have h_k_not_dvd_m_minus_1 : ∀ k ∈ Finset.Icc m n, ¬k ∣ m - 1 := by
      intros k hk
      rw [Finset.mem_Icc] at hk
      apply Nat.not_dvd_of_pos_of_lt
      · omega
      · omega
    aesop
    -- Combining the above, $m - 1$ satisfies the set definition.
  -- Part $2$: Prove $m - 1$ is the maximum element, i.e., any $d$ ∈ set satisfies $d ≤ m - 1$.
  · intros d hd
    -- Decompose $d$ into prime factors: $d = p_1 * p_2 * ... * p_t$.
    let t := (Nat.primeFactorsList d).length
    let primes := Nat.primeFactorsList d
    have h_d_eq : d = primes.prod := by
      have h_d_ne_zero : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd.1
      have h_norm : d = (UniqueFactorizationMonoid.normalizedFactors d).prod := by
        have h_assoc := UniqueFactorizationMonoid.prod_normalizedFactors h_d_ne_zero
        rcases h_assoc with ⟨u, hu⟩
        have h_u_eq_one : u = 1 := by
          exact Nat.units_eq_one u
        rw [h_u_eq_one] at hu
        simp [Units.val_one, mul_one] at hu
        exact hu.symm
      have h_factors_eq : UniqueFactorizationMonoid.normalizedFactors d = ↑(Nat.primeFactorsList d) := Nat.factors_eq d
      rw [h_factors_eq] at h_norm
      exact h_norm
    -- Case $1$: $t = 0$, i.e.,$d = 1$.
    have h_t_zero : t = 0 → d ≤ m - 1 := by
      intros h_t
      have h_primes_nil : primes = [] := by
        rw [← List.length_eq_zero, ← h_t]
      rw [h_primes_nil, List.prod_nil] at h_d_eq
      rw [h_d_eq]
      exact Nat.le_sub_one_of_lt (by linarith[hm])
    -- If $t = 0$, the conclusion holds; next, assume $t ≥ 1$.
    by_cases h_t_pos : t ≥ 1
    · -- Prove all $p_i ≤ m - 1$.
      have h_primes_le_m_minus_1 : ∀ {i} (hi : i < t), primes.get ⟨i, hi⟩ ≤ m - 1 := by
        intros i hi
        have h_pi_dvd_n_fact : primes.get ⟨i, hi⟩ ∣ Nat.factorial n := by
          apply Nat.dvd_trans
          · apply List.dvd_prod
            exact List.get_mem primes ⟨i, hi⟩
          · rw [← h_d_eq]
            exact hd.2.1
        have h_pi_not_in_m_n : primes.get ⟨i, hi⟩ ∉ Finset.Icc m n := by
          intro h_contr
          apply hd.2.2 (primes.get ⟨i, hi⟩) h_contr
          rw [h_d_eq]
          exact List.dvd_prod (List.get_mem primes ⟨i, hi⟩)
        have h_pi_le_n : primes.get ⟨i, hi⟩ ≤ n := by
          have h_mem : primes.get ⟨i, hi⟩ ∈ Nat.primeFactorsList d := List.get_mem primes ⟨i, hi⟩
          have hp : (primes.get ⟨i, hi⟩).Prime := Nat.prime_of_mem_primeFactorsList h_mem
          have h_dvd : primes.get ⟨i, hi⟩ ∣ Nat.factorial n := h_pi_dvd_n_fact
          have h_le_n : primes.get ⟨i, hi⟩ ≤ n := by
            have hp : (primes.get ⟨i, hi⟩).Prime := Nat.prime_of_mem_primeFactorsList (List.get_mem primes ⟨i, hi⟩)
            have h_dvd_iff_le : primes.get ⟨i, hi⟩ ∣ n.factorial ↔ primes.get ⟨i, hi⟩ ≤ n := Nat.Prime.dvd_factorial hp
            exact h_dvd_iff_le.mp h_pi_dvd_n_fact
          exact h_le_n
        rw [Finset.mem_Icc, not_and_or, not_le] at h_pi_not_in_m_n
        cases h_pi_not_in_m_n with
        | inl h => exact Nat.le_pred_of_lt h
        | inr h => exact False.elim (h h_pi_le_n)
      -- Consider $p_1, p_1*p_2, ..., p_1*...*p_t$, which are all divisors of $d$.
      have h_divisors : ∀ j ≤ t, j > 0 → (List.take j primes).prod ≤ m - 1 := by
        intros j hj_le hj_pos
        by_contra h_not_le
        have h_sj_gt_m_minus_1 : (List.take j primes).prod > m - 1 := Nat.not_le.mp h_not_le
        -- Find the smallest $j'$ such that $(List.take j' primes).prod > m - 1$.
        let P : ℕ → Prop := fun j' => (List.take j' primes).prod > m - 1
        have h_exists : ∃ j', P j' := by
          use j
        have h_exists : ∃ j', (List.take j' primes).prod > m - 1 := by
          use j
        let j' := Nat.find h_exists
        have h_j'_gt : (List.take j' primes).prod > m - 1 := Nat.find_spec h_exists
        have h_j'_minimal : ∀ k < j', (List.take k primes).prod ≤ m - 1 := by
          intros k hk
          apply Nat.le_of_not_lt
          intro h_contr
          apply Nat.find_min h_exists hk
          exact h_contr
        -- Prove $j' > t$ (otherwise leads to contradiction).
        have h_j'_eq_t : j' > t := by
          by_contra h_ne_t
          have h_j'_le_t : j' ≤ t := by omega
          have h_s_j'_ge_m : (List.take j' primes).prod ≥ m := by omega
          have h_s_j'_le_n : (List.take j' primes).prod ≤ n := by
            by_cases h_j'_pos : j' > 0
            · let s_j'_minus_1 := (List.take (j' - 1) primes).prod
              have h_j'_minus_1_lt_t : j' - 1 < t := by omega
              have h_s_j'_eq : (List.take j' primes).prod = s_j'_minus_1 * primes.get ⟨j' - 1, h_j'_minus_1_lt_t⟩ := by
                have h_j'_eq_succ : j' = j' - 1 + 1 := by omega
                have h_take_succ : List.take j' primes = List.take (j' - 1) primes ++ [primes.get ⟨j' - 1, h_j'_minus_1_lt_t⟩] := by
                  have h_take_j'_succ : List.take j' primes = List.take (j' - 1 + 1) primes := by tauto
                  calc
                    List.take j' primes = List.take (j' - 1 + 1) primes := h_take_j'_succ
                    _ = List.take (j' - 1) primes ++ [primes.get ⟨j' - 1, h_j'_minus_1_lt_t⟩] := by simp [List.take_append_of_le_length h_j'_le_t]
                rw [h_take_succ, List.prod_append, List.prod_singleton]
              have h_s_j'_minus_1_le_m_minus_1 : s_j'_minus_1 ≤ m - 1 := h_j'_minimal (j' - 1) (Nat.sub_lt h_j'_pos (Nat.le_refl 1))
              calc
                (List.take j' primes).prod = s_j'_minus_1 * primes.get ⟨j' - 1, h_j'_minus_1_lt_t⟩ := h_s_j'_eq
                _ ≤ (m - 1) * primes.get ⟨j' - 1, h_j'_minus_1_lt_t⟩ := Nat.mul_le_mul_right _ h_s_j'_minus_1_le_m_minus_1
                _ ≤ (m - 1) * (m - 1) := Nat.mul_le_mul_left _ (h_primes_le_m_minus_1 h_j'_minus_1_lt_t)
                _ = m * (m - 2) + 1 := by
                  have h₁ : m ≥ 2 := by linarith
                  cases m with
                  | zero => contradiction
                  | succ m =>
                    cases m with
                    | zero => contradiction
                    | succ m =>
                      simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul]
                      ring_nf at *
                _ ≤ n := by omega
            · have h_j'_eq_0 : j' = 0 := Nat.eq_zero_of_not_pos h_j'_pos
              simp [h_j'_eq_0, List.take_zero, List.prod_nil] at h_j'_gt
              have h_contradiction : False := by omega
              contradiction
          -- $s_j' ∈ [m, n]$ leads to contradiction.
          have h_s_j'_in_m_n : (List.take j' primes).prod ∈ Finset.Icc m n := by simp [Finset.mem_Icc, h_s_j'_ge_m, h_s_j'_le_n]
          have h_s_j'_dvd_d : (List.take j' primes).prod ∣ d := by
            rw [h_d_eq]
            apply List.Sublist.prod_dvd_prod
            apply List.take_sublist
          exact hd.2.2 (List.take j' primes).prod h_s_j'_in_m_n h_s_j'_dvd_d
        -- Thus $j' > t$, so $(List.take j primes).prod ≤ m - 1$.
        have h_j_le_t : j ≤ t := hj_le
        have h_j_lt_j' : j < j' := by omega
        have h_j_le_m_minus_1 : (List.take j primes).prod ≤ m - 1 := h_j'_minimal j h_j_lt_j'
        contradiction
      -- Derive $j = t$ to obtain $d ≤ m - 1$.
      have h_d_le_m_minus_1 : d ≤ m - 1 := by
        rw [h_d_eq]
        have h_take_t_eq : List.take t primes = primes := by
          unfold t primes
          apply List.take_length
        rw [← h_take_t_eq]
        apply h_divisors t (Nat.le_refl t) h_t_pos
      exact h_d_le_m_minus_1
    · -- If $t < 1$, then $t = 0$.
      have h_t_zero_case : t = 0 := by
        exact Nat.eq_zero_of_not_pos h_t_pos
      exact h_t_zero h_t_zero_case