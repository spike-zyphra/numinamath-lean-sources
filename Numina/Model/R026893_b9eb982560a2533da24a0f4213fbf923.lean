import Mathlib

theorem number_theory_12482 (a : ℕ → ℕ) (m : ℕ) (apos : 0 < m) (ha1 : a 1 = m) (han : ∀ n : ℕ, a (n + 1) = if 2 ∣ (a n) then a n / 2 else 3 * a n + 1) :
    a 4 = 7 ↔ m = 9 ∨ m = 56 := by
  constructor
  · -- Assume a 4 = 7, prove m = 9 ∨ m = 56
    intro h
    have ha2 : a 2 = if 2 ∣ (a 1) then a 1 / 2 else 3 * (a 1) + 1 := by
      specialize han 1
      simpa using han
    have ha3 : a 3 = if 2 ∣ (a 2) then a 2 / 2 else 3 * (a 2) + 1 := by
      specialize han 2
      simpa using han
    have ha4 : a 4 = if 2 ∣ (a 3) then a 3 / 2 else 3 * (a 3) + 1 := by
      specialize han 3
      simpa using han
    rw [ha4] at h
    by_cases h1 : 2 ∣ (a 3)
    · -- a 4 = a 3 / 2 = 7
      simp [h1] at h
      have h2 : a 3 = 14 := by
        omega
      rw [ha3] at h2
      by_cases h3 : 2 ∣ (a 2)
      · -- a 3 = a 2 / 2 = 14
        simp [h3] at h2
        have h4 : a 2 = 28 := by
          omega
        rw [ha2] at h4
        by_cases h5 : 2 ∣ (a 1)
        · -- a 2 = a 1 / 2 = 28
          simp [h5] at h4
          have h6 : a 1 = 56 := by
            omega
          rw [ha1] at h6
          right
          omega
        · -- a 2 = 3 * a 1 + 1 = 28
          simp [h5] at h4
          have h7 : a 1 = 9 := by
            omega
          rw [ha1] at h7
          left
          omega
      · -- a 3 = 3 * a 2 + 1 = 14
        simp [h3] at h2
        omega
    · -- a 4 = 3 * a 3 + 1 = 7
      simp [h1] at h
      have h3_eq : a 3 = 2 := by
        omega
      omega
  · -- m = 9 ∨ m = 56, prove a 4 = 7
    rintro (h | h)
    · -- m = 9
      have ha1' : a 1 = 9 := by
        linarith [ha1, h]
      have ha2 : a 2 = 28 := by
        rw [han 1]
        rw [ha1']
        norm_num [Nat.dvd_iff_mod_eq_zero]
      have ha3 : a 3 = 14 := by
        rw [han 2]
        rw [ha2]
        norm_num [Nat.dvd_iff_mod_eq_zero]
      have ha4 : a 4 = 7 := by
        rw [han 3]
        rw [ha3]
        norm_num [Nat.dvd_iff_mod_eq_zero]
      linarith
    · -- m = 56
      have ha1' : a 1 = 56 := by
        linarith [ha1, h]
      have ha2 : a 2 = 28 := by
        rw [han 1]
        rw [ha1']
        norm_num [Nat.dvd_iff_mod_eq_zero]
      have ha3 : a 3 = 14 := by
        rw [han 2]
        rw [ha2]
        norm_num [Nat.dvd_iff_mod_eq_zero]
      have ha4 : a 4 = 7 := by
        rw [han 3]
        rw [ha3]
        norm_num [Nat.dvd_iff_mod_eq_zero]
      linarith