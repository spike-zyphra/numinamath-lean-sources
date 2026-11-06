import Mathlib

theorem number_theory_177417 (a : ℕ) :
    (a + 11) % (a - 9) = 0 ↔
    a = 10 ∨ a = 11 ∨ a = 13 ∨ a = 14 ∨ a = 19 ∨ a = 29 := by
  constructor
  · -- Forward
    intro h
    by_cases h1 : a ≤ 9
    · -- a ≤ 9, so a - 9 = 0, but then (a + 11) % (a - 9) = a + 11, so we need a + 11 = 0, which is impossible.
      have h2 : a ≤ 9 := h1
      interval_cases a <;> norm_num at h ⊢ <;> omega
    · -- a > 9
      have h2 : a > 9 := by omega
      have h3 : a - 9 > 0 := by omega
      have h5 : a - 9 > 0 := h3
      have h4 : (a - 9) ∣ (a + 11) := by
        have h11 : (a + 11) % (a - 9) = 0 := h
        have : (a - 9) ∣ (a + 11) := by 
          exact Nat.dvd_of_mod_eq_zero h11
        exact this
      -- From $h4 : (a - 9) \mid (a + 11)$, we derive $(a - 9) \mid 20$
      have h5 : (a - 9) ∣ 20 := by
        have h6 : (a - 9) ∣ (a + 11) := h4
        have h7 : (a - 9) ∣ (a - 9) := by
          use 1
          all_goals omega
        have h8 : (a - 9) ∣ ((a + 11) - (a - 9)) := Nat.dvd_sub' h6 h7
        have h9 : (a + 11) - (a - 9) = 20 := by
          omega
        rw [h9] at h8
        exact h8
      have h6 : (a - 9) ≤ 20 := by 
        exact Nat.le_of_dvd (by norm_num) h5
      have h7 : a - 9 ≤ 20 := h6
      have : a ≤ 29 := by
        omega
      interval_cases h8 : a <;> norm_num at *
      <;> omega
  · -- Backward
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num