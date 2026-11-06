import Mathlib

theorem number_theory_207514 (n : ℤ) :
    (n - 7) ∣ (5 * n - 23) ↔ n = -5 ∨ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
    n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 13 ∨ n = 19 := by
  constructor
  · -- Assume (n - 7) divides (5n - 23). Then n is in the given set.
    intro h
    have h1 : (n - 7) ∣ (5 * n - 23) := h
    have h2 : (n - 7) ∣ 12 := by
      have eq1 : 5 * n - 23 = 5 * (n - 7) + 12 := by
        ring
      have eq2 : (n - 7) ∣ (5 * (n - 7)) := by
        use 5
        ring
      have eq3 : (n - 7) ∣ ((5 * (n - 7) + 12)) := by
        have h3 : (5 * (n - 7) + 12) = (5 * n - 23) := by
          linarith
        rw [h3] at *
        exact h1
      have eq4 : (n - 7) ∣ 12 := by
        have h4 : (n - 7) ∣ ((5 * (n - 7) + 12)) := eq3
        have h5 : (n - 7) ∣ (5 * (n - 7)) := eq2
        have h6 : (n - 7) ∣ ((5 * (n - 7) + 12) - (5 * (n - 7))) := by
          apply Dvd.dvd.sub
          · exact h4
          · exact h5
        have h7 : ((5 * (n - 7) + 12) - (5 * (n - 7))) = 12 := by
          ring
        rw [h7] at h6
        exact h6
      exact eq4
    have h3 : (n - 7) ∣ 12 := h2
    have h4 : (n - 7) ≤ 12 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (n - 7) ≥ -12 := by
      have h6 : (- (n - 7)) ∣ 12 := by
        exact Int.neg_dvd.2 h3
      have h7 : - (n - 7) ≤ 12 := by
        apply Int.le_of_dvd (by norm_num) h6
      linarith
    have h6 : n - 7 ≥ -12 := h5
    have h7 : n - 7 ≤ 12 := h4
    have h8 : n ≥ -5 := by
      omega
    have h9 : n ≤ 19 := by
      omega
    interval_cases n <;> norm_num at h1 ⊢ <;> tauto
  · -- Assume n is in the given set. Then (n - 7) divides (5n - 23).
    rintro (h | h | h | h | h | h | h | h | h | h | h | h)
    · -- n = -5
      rw [h]
      norm_num
    · -- n = 1
      rw [h]
      norm_num
    · -- n = 3
      rw [h]
      norm_num
    · -- n = 4
      rw [h]
      norm_num
    · -- n = 5
      rw [h]
      norm_num
    · -- n = 6
      rw [h]
      norm_num
    · -- n = 8
      rw [h]
      norm_num
    · -- n = 9
      rw [h]
      norm_num
    · -- n = 10
      rw [h]
      norm_num
    · -- n = 11
      rw [h]
      norm_num
    · -- n = 13
      rw [h]
      norm_num
    · -- n = 19
      rw [h]
      norm_num