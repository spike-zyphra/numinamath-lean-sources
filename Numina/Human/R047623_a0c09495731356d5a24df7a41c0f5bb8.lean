import Mathlib
open Nat

/- Let $S$ be a finite set of integers, each greater than $1$.  Suppose that for each integer $n$ there is some $s\in S$ such that $\gcd(s,n)=1$ or $\gcd(s,n)=s$.  Show that there exist $s,t\in S$ such that $\gcd(s,t)$ is prime. -/
theorem number_theory_41936 (S : Finset ℕ) (hS : ∀ s ∈ S, s > 1)
    (hS' : ∀ n : ℕ, ∃ s ∈ S, Nat.gcd s n = 1 ∨ Nat.gcd s n = s) :
    ∃ s t, s ∈ S ∧ t ∈ S ∧ Nat.Prime (Nat.gcd s t) := by
    -- Find the smallest $k > 0$ such that $k$ is not coprime with all elements of $S$.
  have h_k_exists : ∃ k > 0, ∀ s ∈ S, Nat.gcd s k ≠ 1 := by
    let lcm_S := S.prod id
    have h_lcm_pos : lcm_S > 0 := by
      apply Finset.prod_pos
      intro s hs
      exact lt_of_lt_of_le (by norm_num) (hS s hs)
    use lcm_S
    constructor
    · exact h_lcm_pos
    · intro s hs
      have h_dvd : s ∣ lcm_S := Finset.dvd_prod_of_mem id hs
      have h_gcd_eq_s : Nat.gcd s lcm_S = s := by
        apply Nat.gcd_eq_left
        exact h_dvd
      have h_s_gt_1 : s > 1 := hS s hs
      rw [h_gcd_eq_s]
      have h_s_ne_1 : s ≠ 1 := by linarith
      exact h_s_ne_1
  let k := Nat.find h_k_exists
  have h_k_spec : k > 0 ∧ ∀ s ∈ S, Nat.gcd s k ≠ 1 := by
    exact Nat.find_spec h_k_exists
  have h_k_pos : k > 0 := (Nat.find_spec h_k_exists).1
  -- There exists $n ∈ S$ that divides $k$.
  have h_n_exists : ∃ n ∈ S, n ∣ k := by
    specialize hS' k
    rcases hS' with ⟨n, hnS, h_gcd⟩
    cases h_gcd with
    | inl h_gcd_eq_one =>
      have h_gcd_n_k_ne_1 : Nat.gcd n k ≠ 1 := h_k_spec.2 n hnS
      contradiction
    | inr h_gcd_eq_n =>
      use n, hnS
      rw [← h_gcd_eq_n]
      apply Nat.gcd_dvd_right
  rcases h_n_exists with ⟨n, hnS, h_n_dvd_k⟩
  -- If $n$ is prime, then $gcd(n, n) = n$ is prime.
  by_cases h_n_prime : Nat.Prime n
  · use n, n
    have : n.gcd n = n := by apply Nat.gcd_self
    rw [← this] at h_n_prime
    exact ⟨hnS, hnS, h_n_prime⟩
  -- Otherwise, take a prime $p$ dividing $n$.
  have h_n_not_prime : ¬Nat.Prime n → ∃ p, Nat.Prime p ∧ p ∣ n := by
    intro h_not_prime
    have h_n_ge_2 : n ≥ 2 := by
      have h_n_gt_1 : n > 1 := hS n hnS
      exact Nat.le_of_lt_succ (Nat.succ_lt_succ h_n_gt_1)
    have h_n_factors : ∃ p, Nat.Prime p ∧ p ∣ n := by
      apply Nat.exists_prime_and_dvd (n := n)
      have : n ≠ 1 := by omega
      exact this
    exact h_n_factors
  rcases h_n_not_prime h_n_prime with ⟨p, h_p_prime, h_p_dvd_n⟩
  -- Consider $k/p$, which is less than $k$.
  have h_k_div_p : p ∣ k := by
    apply Nat.dvd_trans h_p_dvd_n h_n_dvd_k
  have h_k_div_p_pos : k / p > 0 := by
    apply Nat.div_pos
    · exact le_of_dvd h_k_pos h_k_div_p
    · exact Nat.Prime.pos h_p_prime
  have h_k_div_p_lt_k : k / p < k := by
    apply Nat.div_lt_self h_k_pos
    exact Nat.Prime.one_lt h_p_prime
  -- By minimality of $k$, $k/p$ is coprime with some $n' ∈ S$.
  have h_k_div_p_coprime : ∃ n' ∈ S, Nat.gcd n' (k / p) = 1 := by
    have h_k_minimal : ∀ m, m > 0 → m < k → ∃ s ∈ S, Nat.gcd s m = 1 := by
      intro m h_m_pos h_m_lt_k
      have h_not_all_not_coprime : ¬∀ s ∈ S, Nat.gcd s m ≠ 1 := by
        intro h_contra
        have h_m_not_k : m < Nat.find h_k_exists := h_m_lt_k
        have h_m_k_spec : ¬(m > 0 ∧ ∀ s ∈ S, Nat.gcd s m ≠ 1) := Nat.find_min h_k_exists h_m_not_k
        have h_m_not_coprime : m > 0 ∧ ∀ s ∈ S, Nat.gcd s m ≠ 1 := ⟨h_m_pos, h_contra⟩
        contradiction
      push_neg at h_not_all_not_coprime
      exact h_not_all_not_coprime
    exact h_k_minimal (k / p) h_k_div_p_pos h_k_div_p_lt_k
  rcases h_k_div_p_coprime with ⟨n', hn'S, h_gcd_n'_k_div_p⟩
  -- Show that $p$ divides $n'$.
  have h_p_dvd_n' : p ∣ n' := by
    by_contra h_not_p_dvd_n'
    have h_k_eq_p_mul_k_div_p : k = p * (k / p) := by
      rw [eq_comm]
      apply Nat.mul_div_cancel'
      exact h_k_div_p
    have h_gcd_n'_k_eq_one : Nat.gcd n' k = 1 := by
      rw [h_k_eq_p_mul_k_div_p]
      apply Nat.Coprime.mul_right
      · have : Nat.Coprime p n' := Iff.mpr (Nat.Prime.coprime_iff_not_dvd h_p_prime) h_not_p_dvd_n'
        exact Nat.coprime_comm.mp this
      · exact h_gcd_n'_k_div_p
    have h_gcd_n'_k_ne_one : Nat.gcd n' k ≠ 1 := h_k_spec.2 n' hn'S
    contradiction
  -- Show that $gcd(n, n') = p$.
  have h_gcd_n_n'_eq_p : Nat.gcd n n' = p := by
    apply Nat.dvd_antisymm
    · have h_gcd_n'_k_eq_p : Nat.gcd n' k = p := by
        apply Nat.dvd_antisymm
        · have h_gcd_dvd_k : Nat.gcd n' k ∣ k := Nat.gcd_dvd_right n' k
          have h_k_eq_p_mul_k_div_p : k = p * (k / p) := by
            rw [eq_comm]
            apply Nat.mul_div_cancel'
            exact h_k_div_p
          have h_gcd_n'_k_dvd_p : Nat.gcd n' k ∣ p := by
            have h_gcd_dvd_p_k_div_p : Nat.gcd n' k ∣ p * (k / p) := by
              rw [← h_k_eq_p_mul_k_div_p]
              exact h_gcd_dvd_k
            have h_gcd_n'_k_coprime_k_div_p : Nat.Coprime (Nat.gcd n' k) (k / p) := by
              rw [Nat.coprime_iff_gcd_eq_one]
              have h_gcd_dvd_gcd_n'_k_p : Nat.gcd (Nat.gcd n' k) (k / p) ∣ Nat.gcd n' (k / p) := by
                apply gcd_dvd_gcd (Nat.gcd_dvd_left n' k) (Nat.dvd_refl (k / p))
              rw [h_gcd_n'_k_div_p] at h_gcd_dvd_gcd_n'_k_p
              exact Nat.dvd_one.mp h_gcd_dvd_gcd_n'_k_p
            apply Nat.Coprime.dvd_of_dvd_mul_right h_gcd_n'_k_coprime_k_div_p h_gcd_dvd_p_k_div_p
          exact h_gcd_n'_k_dvd_p
        · apply Nat.dvd_gcd h_p_dvd_n' h_k_div_p
      have h_gcd_n_n'_dvd_n' : Nat.gcd n n' ∣ n' := Nat.gcd_dvd_right n n'
      have h_gcd_n_n'_dvd_k : Nat.gcd n n' ∣ k := by
        apply Nat.dvd_trans (Nat.gcd_dvd_left n n') h_n_dvd_k
      have h_n_n'_dvd_n_k : Nat.gcd n n' ∣ Nat.gcd n' k := by
        apply Nat.dvd_gcd h_gcd_n_n'_dvd_n' h_gcd_n_n'_dvd_k
      rw [h_gcd_n'_k_eq_p] at h_n_n'_dvd_n_k
      exact h_n_n'_dvd_n_k
    · apply Nat.dvd_gcd h_p_dvd_n h_p_dvd_n'
  -- Conclusion.
  use n, n'
  rw [h_gcd_n_n'_eq_p]
  exact ⟨hnS, hn'S, h_p_prime⟩
