import Mathlib
open Nat

/-Marty and three other people took a math test. Everyone got a non-negative integer score. The average score was 20. Marty was told the average score and concluded that everyone else scored below average. What was the minimum possible score Marty could have gotten in order to definitively reach this conclusion?-/
theorem Logic_theory_612345 :
  IsLeast {m : ℕ | ∀ s : ℕ × ℕ × ℕ, s.1 + s.2.1 + s.2.2 = 80 - m → s.1 < 20 ∧ s.2.1 < 20 ∧ s.2.2 < 20} 61 := by
  -- Define the set $S$ of scores m ensuring all other scores are below $20$.
  let S := {m : ℕ | ∀ s : ℕ × ℕ × ℕ, s.1 + s.2.1 + s.2.2 = 80 - m → s.1 < 20 ∧ s.2.1 < 20 ∧ s.2.2 < 20}
  constructor
  -- Prove $61 ∈ S$, i.e., when $m = 61, s.1, s.2.1, s.2.2 < 20$.
  · intro s h_sum
    have h_s_sum : s.1 + s.2.1 + s.2.2 = 19 := by omega
    have h_s1_le_19 : s.1 ≤ 19 := by omega
    have h_s2_le_19 : s.2.1 ≤ 19 := by omega
    have h_s3_le_19 : s.2.2 ≤ 19 := by omega
    exact ⟨Nat.lt_succ_of_le h_s1_le_19, Nat.lt_succ_of_le h_s2_le_19, Nat.lt_succ_of_le h_s3_le_19⟩
  -- Prove $∀ m ∈ S$, $m ≥ 61$, using proof by contradiction.
  · intro m hm
    by_contra h_m_lt_61
    have h_m_le_60 : m ≤ 60 := by omega
    -- Construct counterexample $s = (0, 0, 80 - m) with s.2.2 ≥ 20$.
    have h_construct : ∃ s : ℕ × ℕ × ℕ, s.1 + s.2.1 + s.2.2 = 80 - m ∧
        (s.1 ≥ 20 ∨ s.2.1 ≥ 20 ∨ s.2.2 ≥ 20) := by
      use (0, 0, 80 - m)
      constructor
      · simp
        -- exact Nat.sub_sub_self h_m_le_60
      · right; right
        have h_80_m_ge_20 : 80 - m ≥ 20 := by omega
        exact h_80_m_ge_20
    -- The counterexample leads to a contradiction.
    rcases h_construct with ⟨s, h_sum, h_ge_20⟩
    have h_s_lt_20 : s.1 < 20 ∧ s.2.1 < 20 ∧ s.2.2 < 20 := hm s h_sum
    cases h_ge_20 with
    | inl h_s1 => linarith
    | inr h_s2_or_s3 => cases h_s2_or_s3 with
      | inl h_s2 => linarith
      | inr h_s3 => linarith