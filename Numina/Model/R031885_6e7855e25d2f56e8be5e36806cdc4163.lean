import Mathlib

theorem algebra_10173 : IsGreatest { m : ℕ | m < 100 ∧ ∃ r x, r > 2 ∧ x > 1 ∧ r * x + 2 = m ∧ (r - 2) * (x + 1) = m } 98 := by
  constructor
  · -- Show that 98 is in the set.
    constructor
    · norm_num
    · use 16, 6
      all_goals norm_num
  · -- Show that 98 is greatest in the set.
    intro m hm
    rcases hm with ⟨hm1, r, x, hr1, hx1, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : m < 100 := hm1
    have h4 : m > 98 := by linarith
    have h5 : m = 99 := by omega
    have eq1 : r * x + 2 = m := by linarith
    have eq2 : (r - 2) * (x + 1) = m := by linarith
    rw [h5] at eq1 eq2
    have eq3 : r * x = 97 := by
      omega
    have eq4 : (r - 2) * (x + 1) = 99 := by
      omega
    have hr2 : r ≤ 97 := by
      by_contra h
      push_neg at h
      have h8 : x ≤ 1 := by
        nlinarith [h, eq3]
      omega
    have hx2 : x ≤ 97 := by
      by_contra h
      push_neg at h
      have h7 : r ≤ 1 := by
        nlinarith [h, eq3]
      omega
    interval_cases r <;> omega