import Mathlib
open Nat Real Finset Set
noncomputable section

/-6. Let $S$ be the set of rational numbers satisfying the following conditions:
(1) If $a \in S, b \in S$, then $a+b \in S, a b \in S$;
(2) For any rational number $r$, exactly one of the three relations holds: $r \in S, -r \in S, r=0$. Prove that $S$ is the set of all positive rational numbers.-/
theorem number_theory_600123 (S : Set ℚ)
  (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ x * y ∈ S)
  (hS' : ∀ r : ℚ, (r ∈ S ∨ -r ∈ S ∨ r = 0) ∧ ¬(r ∈ S ∧ -r ∈ S) ∧ ¬(r ∈ S ∧ r = 0) ∧ ¬(-r ∈ S ∧ r = 0)) :
  S = {x | 0 < x} := by
  apply Set.ext
  intro x
  -- Prove: If $x > 0$, then $x ∈ S$.
  have h_pos_rat : ∀ x : ℚ, x > 0 → x ∈ S := by
    intro x hx
    -- Prove that $r^2 ∈ S$ for any non-zero $r$.
    have h_square : ∀ r : ℚ, r ≠ 0 → r * r ∈ S := by
      intro r hr
      have h_cases := (hS' r).1
      cases h_cases with
      | inl h_r =>
        exact (hS r h_r r h_r).2
      | inr h_cases =>
        cases h_cases with
        | inl h_neg_r =>
          have : r * r = (-r) * (-r) := by ring
          rw [this]
          exact (hS (-r) h_neg_r (-r) h_neg_r).2
        | inr h_zero =>
          exact absurd h_zero hr
    -- Prove that $1 ∈ S$.
    have h_one : 1 ∈ S := by
      have h₁ : (1 : ℚ) ≠ 0 := by norm_num
      have h₂ : (1 : ℚ) * (1 : ℚ) = 1 := by norm_num
      rw [← h₂]
      exact h_square 1 h₁
    -- Prove that positive integers (as rationals) are in $S$.
    have h_pos_int : ∀ n : ℕ, n ≠ 0 → (n : ℚ) ∈ S := by
      intro n hn
      induction n with
      | zero =>
        contradiction
      | succ n' ih =>
        cases n' with
        | zero =>
          simp
          exact h_one
        | succ m =>
          have h₁ : m + 1 ≠ 0 := by norm_num
          have h_ind : (m + 1 : ℚ) ∈ S := by
            exact_mod_cast ih h₁
          have h₂ : (m + 1 + 1 : ℚ) = (m + 1 : ℚ) + 1 := by norm_cast
          show (succ (succ m) : ℚ) ∈ S
          have h₃ : (succ (succ m) : ℚ) = (m + 1 + 1 : ℚ) := by
            simp [Nat.succ_eq_add_one]
          rw [h₃, h₂]
          exact (hS (m + 1) h_ind 1 h_one).1
    -- Prove that $1/(q*q) ∈ S$ for non-zero natural $q$.
    have h_inv_square : ∀ q : ℕ, q ≠ 0 → (1 / (q * q) : ℚ) ∈ S := by
      intro q hq
      have h₁ : (q : ℚ) ≠ 0 := by norm_cast
      have h₂ : (q : ℚ) * (q : ℚ) ∈ S := h_square q h₁
      have h₃ : (q : ℚ) * (q : ℚ) = (q * q : ℚ) := by norm_cast
      have h₄ : (q * q : ℚ) ∈ S := by rw [← h₃]; exact h₂
      have h₅ : (q * q : ℚ) ≠ 0 := by norm_cast; exact Nat.mul_ne_zero hq hq
      have h₆ : (1 / (q * q) : ℚ) = (1 / (q * q : ℚ)) := by norm_cast
      have h₇ : (1 / q : ℚ) * (1 / q : ℚ) ∈ S := by
        have h₈ : (1 / q : ℚ) ≠ 0 := by field_simp [h₁]
        exact h_square (1 / q) h₈
      have h₈ : (1 / q : ℚ) * (1 / q : ℚ) = (1 / (q * q) : ℚ) := by
        field_simp [h₁]
      have h₉ : (1 / (q * q) : ℚ) ∈ S := by rw [← h₈]; exact h₇
      exact h₆ ▸ h₉
    -- Prove that positive rationals $p/q ∈ S$.
    have h_pos_rat : ∀ p q : ℕ, p ≠ 0 → q ≠ 0 → (p / q : ℚ) ∈ S := by
      intro p q hp hq
      have h₁ : (p : ℚ) ∈ S := h_pos_int p hp
      have h₂ : (q : ℚ) ∈ S := h_pos_int q hq
      have h₃ : (1 / (q * q) : ℚ) ∈ S := h_inv_square q hq
      have h₄ : (p : ℚ) * (q : ℚ) ∈ S := (hS p h₁ q h₂).2
      have h₅ : (p : ℚ) * (q : ℚ) = (p * q : ℚ) := by norm_cast
      have h₄' : (p * q : ℚ) ∈ S := by rw [← h₅]; exact h₄
      have h₆ : (p / q : ℚ) = (p * q : ℚ) * (1 / (q * q) : ℚ) := by
        field_simp; norm_cast; ring_nf
      rw [h₆]
      exact (hS (p * q) h₄' (1 / (q * q)) h₃).2
    -- Prove that any positive rational $x ∈ S$.
    have h_x_pos_rat : x > 0 → x ∈ S := by
      intro h
      have h_rat : (x.num : ℚ) / x.den = x := Rat.num_div_den x
      have h_den_pos : x.den > 0 := Rat.den_pos x
      have h_num_pos : x.num > 0 := by
        have h₁ : (x.num : ℚ) / x.den > 0 := by nlinarith
        have h₂ : (x.den : ℚ) > 0 := by exact_mod_cast h_den_pos
        have : (x.num : ℚ) > 0 := by tauto
        exact Int.cast_pos.mp this
      have h_p : x.num.toNat ≠ 0 := by omega
      have h_q : x.den ≠ 0 := by omega
      have h_pq : (x.num.toNat / x.den : ℚ) ∈ S := h_pos_rat x.num.toNat x.den h_p h_q
      have h_eq : (x.num.toNat / x.den : ℚ) = x := by
        have h₁ : (x.num : ℚ) = (x.num.toNat : ℚ) := by
          have : x.num ≥ 0 := le_of_lt h_num_pos
          have : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg this
          tauto
        have h₂ : (x.num.toNat / x.den : ℚ) = (x.num : ℚ) / x.den := by
          rw [h₁]
        rw [← h_rat] at h₂
        have : (x.num.toNat / x.den : ℚ) = x := by
          rw [← h_rat, h₂]
          simp only [Rat.num_div_den]
        rw [this]
      rw [h_eq] at h_pq
      exact h_pq
    exact h_x_pos_rat hx
  -- Prove $x ∈ S ↔ x > 0$.
  have h_iff : x ∈ S ↔ x > 0 := by
    constructor
    · -- Prove: If $x ∈ S$, then $x > 0$.
      intro hx
      have h_not_zero : x ≠ 0 := by
        have h₁ : ¬(x ∈ S ∧ x = 0) := (hS' x).2.2.1
        intro h_zero
        have h₂ : x ∈ S ∧ x = 0 := ⟨hx, h_zero⟩
        exact h₁ h₂
      have h_not_neg : ¬(-x ∈ S) := by
        have h₁ : ¬(x ∈ S ∧ -x ∈ S) := (hS' x).2.1
        intro h_neg
        have h₂ : x ∈ S ∧ -x ∈ S := ⟨hx, h_neg⟩
        exact h₁ h₂
      have h_pos : x > 0 := by
        by_contra h_npos
        have h_neg_or_zero : x < 0 ∨ x = 0 := by
          have h_le_zero : x ≤ 0 := by simpa using h_npos
          exact le_iff_lt_or_eq.mp h_le_zero
        cases h_neg_or_zero with
        | inr h_zero => exact h_not_zero h_zero
        | inl h_neg =>
          have h_minus_x_pos : -x > 0 := by linarith
          have h_minus_x_in_S : -x ∈ S := h_pos_rat (-x) h_minus_x_pos
          exact h_not_neg h_minus_x_in_S
      exact h_pos
    · -- Prove: If $x > 0$, then $x ∈ S$.
      intro hx
      exact h_pos_rat x hx
  -- Conclude set equality using h_iff.
  exact h_iff
