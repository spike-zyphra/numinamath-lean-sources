import Mathlib

theorem number_theory_17114 :
    IsLeast {b | 3 < b ∧ ∃ k, k^2 = Nat.ofDigits b [3, 2]} 11 := by
  constructor
  · -- Show that 11 is in the set.
    constructor
    · norm_num
    · use 5
      native_decide
  · -- Show that no smaller base is in the set
    intro b ⟨hb1, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h1 : b < 11 := h
    have h2 : b ≥ 4 := by omega
    have eq1 : Nat.ofDigits b [3, 2] = 2 * b + 3 := by
      simp [Nat.ofDigits, mul_add, mul_one]
      <;> ring_nf
      all_goals omega
    rw [eq1] at hk
    have h3 : k^2 = 2 * b + 3 := hk
    have h4 : b < 11 := h
    have h6 : k ≤ 4 := by
      nlinarith [show 2 * b + 3 ≤ 2 * 10 + 3 by omega]
    interval_cases k <;> interval_cases b <;> omega