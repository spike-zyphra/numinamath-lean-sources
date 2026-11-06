import Mathlib
open Real Finset Set Complex

-- Define the sequence $a_n$.Natural numbers include $0$, and defining $a_0 = 1$ does not affect the conclusion.
noncomputable def a : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => 1 + a (n + 1) / a (n + 2)

-- Prove that $a_n$ is greater than $0$, ensuring division is well-defined and positive.
lemma a_positive : ∀ n, a n > 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [a]
    | succ n =>
      cases n with
      | zero => simp [a]
      | succ n =>
        cases n with
        | zero => simp [a]
        | succ n =>
          simp [a]
          apply add_pos_of_nonneg_of_pos
          · exact zero_le_one
          · apply div_pos
            · exact ih (n + 1) (by linarith)
            · exact ih (n + 2) (by linarith)

/-10.2. Vasya writes down a sequence of numbers: $a_{1}=1, a_{2}=1, \ldots, a_{n+1}=1+\frac{a_{n-1}}{a_{n}}$ for $n \geq 2$. He noticed that $a_{5}>2$, $a_{6}<2$, $a_{7}>2$, $a_{8}<2$ and made the following hypothesis: all terms of the sequence with odd indices, starting from index 5, are greater than 2, and all terms with even indices, starting from index 4, are less than 2. Prove this hypothesis.-/
theorem algebra_201234 :
    ∀ k, k ≥ 3 → a (2 * k - 1) > 2 ∧ a (2 * k - 2) < 2 := by
  intro k hk
  induction k with
  -- Prove $k ≥ 3$, rule out $k = 0$.
  | zero => contradiction
  | succ k ih =>
    cases lt_or_le k 2 with
    -- Rule out $k < 3$
    | inl h_k_lt_2 => linarith
    | inr h_k_ge_2 =>
      have h_k_succ : k + 1 ≥ 3 := by linarith
      cases eq_or_lt_of_le h_k_succ with
      | inl h_k_eq_3 =>
        -- Induction base case: $k + 1 = 3$, i.e., $k = 2$.
        have h_base : a (2 * (k + 1) - 1) > 2 ∧ a (2 * (k + 1) - 2) < 2 := by
          have : k = 2 := by linarith
          rw [this]
          constructor
          · have h_a3 : a 3 = 2 := by simp [a]; norm_num
            have h_a4 : a 4 = 3 / 2 := by simp [a]; norm_num
            have h_a5 : a 5 = 7 / 3 := by simp [a]; norm_num
            rw [h_a5]
            norm_num
          · have h_a4 : a 4 = 3 / 2 := by simp [a]; norm_num
            rw [h_a4]
            norm_num
        exact h_base
      | inr h_k_gt_3 =>
        -- Induction step: assume true for $k ≥ 3$, prove for $k + 1$.
        have h_assumption : a (2 * k - 1) > 2 ∧ a (2 * k - 2) < 2 := by
          apply ih
          linarith
        -- Induction step $1$: prove $a_(2*(k+1)-2) = 1 + a_(2k-2) / a_(2k-1) < 2$.
        have h_even : a (2 * (k + 1) - 2) < 2 := by
          have h_eq : a (2 * (k + 1) - 2) = a (2 * k) := by tauto
          rw [h_eq]
          have h_index : a (2 * k) = 1 + a (2 * k - 2) / a (2 * k - 1) := by
            have h_index : 2 * k = (2 * k - 3) + 3 := by omega
            rw [h_index, a]
            simp
          rw [h_index]
          have h_div_lt_one : a (2 * k - 2) / a (2 * k - 1) < 1 := by
            have h₁ : 0 < a (2 * k - 1) := by exact a_positive (2 * k - 1)
            apply (div_lt_one h₁).mpr
            exact lt_trans h_assumption.2 h_assumption.1
          nlinarith
        -- Induction step $2$: prove $a_(2*(k+1)-1) = 1 + a_(2k-1) / a_(2k) > 2$.
        have h_odd : a (2 * (k + 1) - 1) > 2 := by
          have h_eq : a (2 * (k + 1) - 1) = a (2 * k + 1) := by tauto
          rw [h_eq]
          have h_index : a (2 * k + 1) = 1 + a (2 * k - 1) / a (2 * k) := by
            have h_index : 2 * k + 1 = (2 * k - 2) + 3 := by omega
            rw [h_index, a]
            simp
            have h₁ : 2 * k - 2 + 1 = 2 * k - 1 := by omega
            have h₂ : 2 * k - 2 + 2 = 2 * k := by linarith
            rw [h₁, h₂]
          rw [h_index]
          have h_div_gt_one : 1 < a (2 * k - 1) / a (2 * k) := by
            have h₁ : 0 < a (2 * k) := by exact a_positive (2 * k)
            apply (one_lt_div h₁).mpr
            exact lt_trans h_even h_assumption.1
          nlinarith
        -- Combine results.
        have h_result : a (2 * (k + 1) - 1) > 2 ∧ a (2 * (k + 1) - 2) < 2 := by
          exact ⟨h_odd, h_even⟩
        exact h_result
