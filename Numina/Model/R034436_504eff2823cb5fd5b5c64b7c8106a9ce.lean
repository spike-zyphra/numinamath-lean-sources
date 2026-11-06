import Mathlib

theorem number_theory_12276 : IsLeast {n : ℕ+ | 17 * n.val ≡ 1234 [MOD 7]} 3 := by

  constructor

  · -- Show 3 is in the set

    show 17 * (3 : ℕ+).val ≡ 1234 [MOD 7]
    native_decide

  · -- Show there is no smaller element in the set

    intro n hn
    have h : 17 * n.val ≡ 1234 [MOD 7] := hn

    have h1 : n.val ≥ 3 := by
      by_contra h2
      push_neg at h2
      have h3 : n.val < 3 := h2
      have : n.val ≥ 1 := by
        exact n.prop
      have h4 : n.val = 1 ∨ n.val = 2 := by
        interval_cases n.val <;> tauto

      rcases h4 with (h5 | h6)
      · -- Case n = 1
        rw [show n.val = 1 by exact h5] at h
        simp [Nat.ModEq] at h

      · -- Case n = 2
        rw [show n.val = 2 by exact h6] at h
        simp [Nat.ModEq] at h

    have h2 : (n : ℕ) ≥ (3 : ℕ) := by
      exact_mod_cast h1

    exact_mod_cast h2