import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_30538 :
  ∃ a b : ℕ → ℝ,
    (∀ i, 3 * π / 2 ≤ a i ∧ a i ≤ b i) ∧
    (∀ i, ∀ x ∈ Ioo 0 1, cos (a i * x) - cos (b i * x) ≥ -1 / i) := by
  use fun _ => 3 * π / 2, fun _ => 3 * π / 2
  constructor
  · -- Show that for all i, a i ≥ 3 * π / 2 and a i ≤ b i
    intro i
    have h1 : 3 * π / 2 ≤ (3 * π / 2 : ℝ) := by
      nlinarith [Real.pi_pos]
    have h2 : (3 * π / 2 : ℝ) ≤ (3 * π / 2 : ℝ) := by
      nlinarith [Real.pi_pos]
    constructor
    · -- Show that a i ≥ 3 * π / 2
      linarith [h1]
    · -- Show that a i ≤ b i
      linarith [h2]
    all_goals try linarith [pi_pos]
  · -- Now, we need to prove the inequality for all i and x in (0, 1)
    intro i x hx
    have h1 : i = 0 ∨ i > 0 := by cases i <;> simp <;> tauto
    rcases h1 with (h1 | h1)
    · -- Case where i = 0
      rw [h1]
      norm_num
      <;> linarith [Real.pi_pos]
    · -- Case where i > 0
      have h2 : (i : ℝ) > 0 := by
        exact_mod_cast show (i : ℝ) > 0 by positivity
      simp [h1] <;> 
        try { 
          have h2 : -1 / (i : ℝ) ≤ 0 := by
            cases i with
            | zero =>
              norm_num
              all_goals linarith [Real.pi_pos]
            | succ n =>
              have h3 : (↑(Nat.succ n) : ℝ) > 0 := by
                have h4 : ↑(Nat.succ n) = (↑n + 1 : ℝ) := by
                  simp [Nat.cast_succ]
                rw [h4]
                have h5 : (↑n : ℝ) ≥ 0 := by
                  exact_mod_cast show (n : ℕ) ≥ 0 by omega
                have h6 : (↑n : ℝ) ≥ 0 := by
                  exact_mod_cast show (n : ℕ) ≥ 0 by omega
                nlinarith
              have h4 : -1 / (↑(Nat.succ n) : ℝ) ≤ 0 := by
                apply div_nonpos_of_nonpos_of_nonneg
                · -- Show -1 ≤ 0
                  norm_num
                · -- Show ↑(Nat.succ n) ≥ 0
                  linarith [h3]
              simpa using h4
          linarith [h2]
        } <;> try { 
          have h7 : (↑i : ℝ) > 0 := by
            exact_mod_cast show i > 0 by
              cases i with
              | zero => tauto
              | succ n => exact Nat.succ_pos n
          tauto
        } <;> try linarith [Real.pi_pos]