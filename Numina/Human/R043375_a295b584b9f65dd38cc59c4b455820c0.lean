import Mathlib
open Nat

/- A natural number $k>1$ is given. The sum of some divisor of $k$ and some divisor of $k - 1$ is equal to $a$,where $a>k + 1$. Prove that at least one of the numbers $a - 1$ or $a + 1$ composite. -/
theorem number_theory_90259 (k a : ℕ) (hk : 1 < k) (ha : a > k + 1)
    (h : ∃ d e, d ∣ k ∧ e ∣ k - 1 ∧ d + e = a) :
    ¬Nat.Prime (a - 1) ∨ ¬Nat.Prime (a + 1) := by
  -- There exist $d$, $e$ satisfying the conditions.
  have h_exists : ∃ d e, d ∣ k ∧ e ∣ k - 1 ∧ d + e = a := h
  rcases h_exists with ⟨d, e, hd_div_k : d ∣ k, he_div_k_minus_1 : e ∣ k - 1, hde_eq_a : d + e = a⟩
  -- Ensure $d$, $e ≥ 1$ (divisors are positive).
  have hd_pos : d ≥ 1 := Nat.pos_of_dvd_of_pos hd_div_k (by linarith)
  have he_pos : e ≥ 1 := by
    have h_k_minus_1_pos : k - 1 > 0 := by omega
    exact Nat.pos_of_dvd_of_pos he_div_k_minus_1 h_k_minus_1_pos

  -- Proof by contradiction: assume both $a - 1$ and $a + 1$ are prime.
  by_contra h_contra
  have h_a_minus_1_prime : Nat.Prime (a - 1) := by
    simp only [not_or, not_not] at h_contra
    exact h_contra.1
  have h_a_plus_1_prime : Nat.Prime (a + 1) := by
    simp only [not_or, not_not] at h_contra
    exact h_contra.2
  -- If $d ≠ k$ and $e ≠ k - 1$, derive a contradiction.
  have h_not_both_small : ¬(d ≠ k ∧ e ≠ k - 1) := by
    intro h_both_small
    -- Prove $d ≤ k / 2$.
    have h_d_le_k_div_2 : d ≤ k / 2 := by
      have h_d_ne_k : d ≠ k := h_both_small.1
      have h_d_dvd_k : d ∣ k := hd_div_k
      rcases h_d_dvd_k with ⟨m, hm⟩
      have h_m_ge_2 : m ≥ 2 := by
        have h_m_ge_1 : m ≥ 1 := Nat.pos_of_ne_zero (by rintro rfl; linarith)
        have h_m_ne_1 : m ≠ 1 := by
          rintro rfl
          rw [mul_one] at hm
          rw [hm] at h_d_ne_k
          exact h_d_ne_k rfl
        exact Nat.succ_le_of_lt (lt_of_le_of_ne h_m_ge_1 h_m_ne_1.symm)
      have h_d_mul_2_le_k : d * 2 ≤ k := by
        calc
          d * 2 = 2 * d := by ring
          _ ≤ m * d := Nat.mul_le_mul_right d h_m_ge_2
          _ = k := by linarith
      omega
    -- Prove $e ≤ (k - 1) / 2$.
    have h_e_le_k_minus_1_div_2 : e ≤ (k - 1) / 2 := by
      have h_e_ne_k_minus_1 : e ≠ k - 1 := h_both_small.2
      have h_e_dvd_k_minus_1 : e ∣ k - 1 := he_div_k_minus_1
      have h_k_minus_1_ge_1 : k - 1 ≥ 1 := by omega
      rcases h_e_dvd_k_minus_1 with ⟨n, hn⟩
      have h_n_ge_2 : n ≥ 2 := by
        have h_n_ge_1 : n ≥ 1 := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hn; linarith)
        have h_n_ne_1 : n ≠ 1 := by
          rintro rfl
          rw [mul_one] at hn
          rw [hn] at h_e_ne_k_minus_1
          exact h_e_ne_k_minus_1 rfl
        exact Nat.succ_le_of_lt (lt_of_le_of_ne h_n_ge_1 h_n_ne_1.symm)
      have h_e_mul_2_le_k_minus_1 : e * 2 ≤ k - 1 := by
        calc
          e * 2 = 2 * e := by ring
          _ ≤ n * e := Nat.mul_le_mul_right e h_n_ge_2
          _ = k - 1 := by linarith
      omega
    have h_a_le_k : a ≤ k := by omega
    have h_a_gt_k : a > k := by linarith
    exact lt_irrefl a (lt_of_le_of_lt h_a_le_k h_a_gt_k)

  -- Either $d = k$ or $e = k - 1$.
  have h_d_eq_k_or_e_eq_k_minus_1 : d = k ∨ e = k - 1 := by omega

  -- Case analysis, proving that when $d = k$, $a - 1$ is composite, and when $e = k - 1$, $a + 1$ is composite.
  have h_conclusion : ¬Nat.Prime (a - 1) ∨ ¬Nat.Prime (a + 1) := by
    cases h_d_eq_k_or_e_eq_k_minus_1 with
    | inl h_d_eq_k =>
      -- Case : $d = k$.
      have h_e_dvd_a_minus_1 : e ∣ a - 1 := by
        rw [← hde_eq_a, h_d_eq_k]
        have : k + e - 1 = (k - 1) + e := by omega
        rw [this]
        exact Nat.dvd_add he_div_k_minus_1 (Nat.dvd_refl e)
      have h_a_minus_1_not_prime : ¬Nat.Prime (a - 1) := by
        have h_a_minus_1_ge_2 : a - 1 ≥ 2 := by omega
        intro h_prime
        have h_e_ne_a_minus_1 : e ≠ a - 1 := by omega
        have h_prime_def : Nat.Prime (a - 1) → ∀ m, m ∣ a - 1 → m = 1 ∨ m = a - 1 := by
          intro h_p
          have : 2 ≤ a - 1 ∧ ∀ m, m ∣ a - 1 → m = 1 ∨ m = a - 1 := Nat.prime_def.mp h_p
          exact this.2
        have h_e_contra : e = 1 ∨ e = a - 1 := by
          apply h_prime_def h_prime
          exact h_e_dvd_a_minus_1
        cases h_e_contra with
        | inl h_e_eq_1 => linarith
        | inr h_e_eq_a_minus_1 => exact h_e_ne_a_minus_1 h_e_eq_a_minus_1
      left
      exact h_a_minus_1_not_prime
    | inr h_e_eq_k_minus_1 =>
      -- Case : $e = k - 1$.
      have h_d_dvd_a_plus_1 : d ∣ a + 1 := by
        rw [← hde_eq_a, h_e_eq_k_minus_1]
        have : d + (k - 1) + 1 = d + k := by omega
        rw [this]
        exact Nat.dvd_add (Nat.dvd_refl d) hd_div_k
      have h_a_plus_1_not_prime : ¬Nat.Prime (a + 1) := by
        have h_a_plus_1_ge_2 : a + 1 ≥ 2 := by linarith
        intro h_prime
        have h_d_ne_a_plus_1 : d ≠ a + 1 := by omega
        have h_prime_def : Nat.Prime (a + 1) → ∀ m, m ∣ a + 1 → m = 1 ∨ m = a + 1 := by
          intro h_p
          have : 2 ≤ a + 1 ∧ ∀ m, m ∣ a + 1 → m = 1 ∨ m = a + 1 := Nat.prime_def.mp h_p
          exact this.2
        have h_d_contra : d = 1 ∨ d = a + 1 := by
          apply h_prime_def h_prime
          exact h_d_dvd_a_plus_1
        cases h_d_contra with
        | inl h_d_eq_1 =>
          have h_d_gt_1 : d > 1 := by
            have h_a_minus_k_minus_1 : a > k + 1 := ha
            rw [← hde_eq_a, h_e_eq_k_minus_1] at h_a_minus_k_minus_1
            omega
          linarith
        | inr h_d_eq_a_plus_1 => exact h_d_ne_a_plus_1 h_d_eq_a_plus_1
      right
      exact h_a_plus_1_not_prime
  -- Construct contradiction using h_conclusion and the prime assumptions.
  cases h_conclusion with
  | inl h_not_prime_a_minus_1 => exact h_not_prime_a_minus_1 h_a_minus_1_prime
  | inr h_not_prime_a_plus_1 => exact h_not_prime_a_plus_1 h_a_plus_1_prime
