import Mathlib
open Finset Set Nat 
noncomputable section

lemma prime_gt_three_mod_six (p : ℕ) (hp : p.Prime) (h_gt_3 : p > 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  -- The remainder modulo $6$ is less than $6$.
  have h_mod_lt : p % 6 < 6 := mod_lt p (by norm_num)
  -- Rule out $p | 6$.
  have h_not_dvd_6 : ¬ 6 ∣ p := by
    intro h_dvd
    have h_dvd_2_or_3 : 2 ∣ p ∨ 3 ∣ p := by omega
    cases h_dvd_2_or_3
    · have : 2 ∣ p := by assumption
      have : p = 2 := (Nat.Prime.dvd_iff_eq hp (by norm_num: 2 ≠ 1)).mp this
      linarith
    · have : 3 ∣ p := by assumption
      have : p = 3 := (Nat.Prime.dvd_iff_eq hp (by norm_num: 3 ≠ 1)).mp this
      linarith
  -- Case analysis on modulo $6$ remainder.
  have h_cases : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by
    omega
  cases h_cases with
  | inl h =>
    -- If $p ≡ 0 (mod 6)$, then $6 ∣ p$, contradicting h_not_dvd_6.
    have h₁ : 6 ∣ p := by
      omega
    contradiction
  | inr h =>
    cases h with
    | inl h =>
      -- If $p ≡ 1 (mod 6)$, return $p ≡ 1 (mod 6)$.
      exact Or.inl h
    | inr h =>
      cases h with
      | inl h =>
        -- If $p ≡ 2 (mod 6)$, then $2 ∣ p$, contradicting $p > 3$$ and $p$ being prime.
        have h₁ : 2 ∣ p := by
          omega
        have h₂ : p = 2 := by
          have : 2 ∣ p := h₁
          have : p = 2 := (Nat.Prime.dvd_iff_eq hp (by norm_num: 2 ≠ 1)).mp this
          exact this
        linarith
      | inr h =>
        cases h with
        | inl h =>
          -- If $p ≡ 3 (mod 6)$, then $3 ∣ p$, contradicting $p > 3$ and $p$ being prime.
          have h₁ : 3 ∣ p := by
            omega
          have h₂ : p = 3 := by
            have : 3 ∣ p := h₁
            have : p = 3 := (Nat.Prime.dvd_iff_eq hp (by norm_num: 3 ≠ 1)).mp this
            exact this
          linarith
        | inr h =>
          cases h with
          | inl h =>
            -- If $p ≡ 4 (mod 6)$, then $2 ∣ p$, contradicting $p > 3$ and $p$ being prime.
            have h₁ : 2 ∣ p := by
              omega
            have h₂ : p = 2 := by
              have : 2 ∣ p := h₁
              have : p = 2 := (Nat.Prime.dvd_iff_eq hp (by norm_num: 2 ≠ 1)).mp this
              exact this
            linarith
          | inr h =>
            -- If $p ≡ 5 (mod 6)$, return $p ≡ 5 (mod 6)$.
            exact Or.inr h

/-## Task 17/77
It is to be proven: If $p_{1}, p_{2}, p_{3}$ are three prime numbers with $p_{i}>3$, of which two form a pair of twin primes, then the product
$$
\prod_{i=1}^{3}\left(p_{i}-1\right)=P
$$
is divisible by a multiple of 48 without a remainder.-/
theorem number_theory_156448
    (p q : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : q.Prime)
    (h_gt_3_p : p > 3) (h_gt_3_q : q > 3) :
    48 ∣ (p - 1) * (p + 1) * (q - 1) := by
  -- $p$ and $p + 2$ form a twin prime pair, $p = 6m₁ - 1$, $p + 2 = 6m₁ + 1$.
  have h_p_form : ∃ m₁, m₁ ≥ 1 ∧ p = 6 * m₁ - 1 ∧ p + 2 = 6 * m₁ + 1 := by
    have h_p_mod : p % 6 = 1 ∨ p % 6 = 5 := prime_gt_three_mod_six p hp h_gt_3_p
    have h_p2_mod : (p + 2) % 6 = 1 ∨ (p + 2) % 6 = 5 := prime_gt_three_mod_six (p + 2) hp2 (by linarith)
    cases h_p_mod with
    | inl h_p_1 =>
      have h_p2_5 : (p + 2) % 6 = 5 := by omega
      exists p / 6 + 1
      omega
    | inr h_p_5 =>
      have h_p2_1 : (p + 2) % 6 = 1 := by omega
      exists (p + 2) / 6
      omega
  obtain ⟨m₁, hm₁_ge_1, h_p, h_p2⟩ := h_p_form
  -- $q = 6m₂ ± 1$.
  have h_q_form : q % 6 = 1 ∨ q % 6 = 5 := prime_gt_three_mod_six q hq h_gt_3_q
  -- Case analysis.
  have h_div_48 : 48 ∣ (p - 1) * (p + 1) * (q - 1) := by
    cases h_q_form with
    | inl h_q_1 =>
      -- Case $1$: $q = 6m₂ + 1$.
      have h_q : q = 6 * (q / 6) + 1 := by omega
      have h_q' : q - 1 = 6 * (q / 6) := by omega
      have h_p2' : p + 1 = 6 * m₁ := by omega
      have h_P : (p - 1) * (p + 1) * (q - 1) = 24 * m₁ * (3 * m₁ - 1) * 3 * (q / 6) := by
        rw [h_p2', h_q', h_p]
        have : (6 * m₁ - 1 - 1) = 2 * (3 * m₁ - 1) := by omega
        rw [this]
        ring
      have h_div_24 : 24 ∣ 24 * m₁ * (3 * m₁ - 1) * 3 * (q / 6) := by
        rw [mul_assoc 24, mul_assoc 24, mul_assoc 24]
        exact dvd_mul_right 24 _
      rw [h_P]
      have h_div_2 : 2 ∣ m₁ ∨ 2 ∣ 3 * m₁ - 1 := by omega
      -- When $2 ∣ m₁$ or $2 ∣ 3 * m₁ - 1$ holds, the product is divisible by $48$.
      cases h_div_2 with
      | inl h_m₁_2 =>
        have h₁: 24 ∣ 24 := by norm_num
        have h₂: 24 * 2 ∣ 24 * m₁ := Nat.mul_dvd_mul h₁ (by assumption)
        have h₃: 24 * 2 = 48 := by norm_num
        have h₄: 24 * 2 ∣ 24 * m₁ * (3 * m₁ - 1) * 3 * (q / 6) := by
          rw [mul_assoc (24 * m₁), mul_assoc (24 * m₁)]
          exact dvd_mul_of_dvd_left h₂ ((3 * m₁ - 1) * 3 * (q / 6))
        simp [h₄]
      | inr h_3m₁_1_2 =>
        have h₁: 24 ∣ 24 := by norm_num
        have h₂: 24 * 2 ∣ 24 * (3 * m₁ - 1) := Nat.mul_dvd_mul h₁ (by assumption)
        have h₃: 24 * 2 = 48 := by norm_num
        have h₄: 24 * 2 ∣ 24 * m₁ * (3 * m₁ - 1) * 3 * (q / 6) := by
          rw [mul_assoc 24, mul_comm m₁, ← mul_assoc, mul_assoc (24 * (3 * m₁ - 1)), mul_assoc (24 * (3 * m₁ - 1))]
          exact dvd_mul_of_dvd_left h₂ (m₁ * 3 * (q / 6))
        simp [h₄]
    | inr h_q_5 =>
      -- Case $2$: $q = 6m₂ - 1$.
      have h_q : q = 6 * (q / 6 + 1) - 1 := by omega
      have h_q' : q - 1 = 2 *(3 * (q / 6 + 1) -1) := by omega
      have h_p2' : p + 1 = 6 * m₁ := by omega
      have h_P : (p - 1) * (p + 1) * (q - 1) = 24 * m₁ * (3 * m₁ - 1) * (3 * (q / 6 + 1) - 1) := by
        rw [h_p2',h_q', h_p]
        have : (6 * m₁ - 1 - 1) = 2 * (3 * m₁ - 1) := by omega
        rw [this]
        ring
      have h_div_24 : 24 ∣ 24 * m₁ * (3 * m₁ - 1) * (3 * (q / 6 + 1) - 1) := by
        rw [mul_assoc 24, mul_assoc 24]
        exact dvd_mul_right 24 _
      rw [h_P]
      have h_div_2 : 2 ∣ m₁ ∨ 2 ∣ 3 * m₁ - 1 := by omega
      -- When $2 ∣ m₁$ or $2 ∣ 3 * m₁ - 1$ holds, the product is divisible by $48$.
      cases h_div_2 with
      | inl h_m₁_2 =>
        have h₁: 24 ∣ 24 := by norm_num
        have h₂: 24 * 2 ∣ 24 * m₁ := Nat.mul_dvd_mul h₁ (by assumption)
        have h₃: 24 * 2 = 48 := by norm_num
        have h₄: 24 * 2 ∣ 24 * m₁ * (3 * m₁ - 1) * (3 * (q / 6 + 1) - 1) := by
          rw [mul_assoc (24 * m₁)]
          exact dvd_mul_of_dvd_left h₂ ((3 * m₁ - 1) * (3 * (q / 6 + 1) - 1))
        simp [h₄]
      | inr h_3m₁_1_2 =>
        have h₁: 24 ∣ 24 := by norm_num
        have h₂: 24 * 2 ∣ 24 * (3 * m₁ - 1) := Nat.mul_dvd_mul h₁ (by assumption)
        have h₃: 24 * 2 = 48 := by norm_num
        have h₄: 24 * 2 ∣ 24 * m₁ * (3 * m₁ - 1) * (3 * (q / 6 + 1) - 1) := by
          rw [mul_assoc 24, mul_comm m₁, ← mul_assoc, mul_assoc (24 * (3 * m₁ - 1))]
          exact dvd_mul_of_dvd_left h₂ (m₁ * (3 * (q / 6 + 1) - 1))
        simp [h₄]
  exact h_div_48
