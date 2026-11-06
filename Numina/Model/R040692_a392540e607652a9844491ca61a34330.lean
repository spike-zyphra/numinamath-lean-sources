import Mathlib

open Nat

theorem number_theory_4712 : IsLeast {x : ℕ | x ≡ 0 [MOD 7] ∧ ∀ n ∈ ({2,3,4,5,6} : Set ℕ), x ≡ 1 [MOD n]} 301 := by
  constructor
  · -- Show that 301 is in the set
    constructor
    · -- 301 ≡ 0 [MOD 7]
      native_decide
    · -- ∀ n ∈ ({2,3,4,5,6} : Set ℕ), 301 ≡ 1 [MOD n]
      intro n hn
      have h2 : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
        simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hn ⊢
        omega
      rcases h2 with (rfl | rfl | rfl | rfl | rfl)
      · -- 301 ≡ 1 [MOD 2]
        native_decide
      · -- 301 ≡ 1 [MOD 3]
        native_decide
      · -- 301 ≡ 1 [MOD 4]
        native_decide
      · -- 301 ≡ 1 [MOD 5]
        native_decide
      · -- 301 ≡ 1 [MOD 6]
        native_decide
  · -- Show that 301 is the smallest
    intro x h
    rcases h with ⟨h7, h⟩
    have h2 : x ≡ 1 [MOD 2] := h 2 (by simp)
    have h3 : x ≡ 1 [MOD 3] := h 3 (by simp)
    have h4 : x ≡ 1 [MOD 4] := h 4 (by simp)
    have h5 : x ≡ 1 [MOD 5] := h 5 (by simp)
    have h6 : x ≡ 1 [MOD 6] := h 6 (by simp)
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num [Nat.ModEq] at h7 h2 h3 h4 h5 h6 <;> all_goals contradiction