import Mathlib

theorem algebra_14324 : {a | ∃ x : ℤ, x^3 + 3 * x^2 + a * x + 7 = 0} = {-71, -27, -11, 9} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if there exists an integer x such that the polynomial equals 0, then a must be in the set.
    rintro ⟨x, hx⟩
    have h1 : x^3 + 3 * x^2 + a * x + 7 = (0 : ℤ) := hx
    have h2 : x ∣ 7 := by
      use (- (x^2 + 3 * x + a))
      linarith
    have h3 : x = 1 ∨ x = -1 ∨ x = 7 ∨ x = -7 := by
      have h4 : x ∣ 7 := h2
      have h5 : x ≤ 7 := by 
        apply Int.le_of_dvd (by norm_num) h4
      have h6 : x ≥ -7 := by
        have h7 : (-x) ∣ 7 := by 
          exact Int.neg_dvd.2 h4
        have h8 : -x ≤ 7 := by 
          apply Int.le_of_dvd (by norm_num) h7
        linarith
      interval_cases x <;> tauto
    rcases h3 with (h4 | h4 | h4 | h4)
    · -- x = 1
      rw [show x = 1 by linarith] at h1
      have ha : a = -11 := by 
        linarith
      simp [ha]
      <;> tauto
    · -- x = -1
      rw [show x = -1 by linarith] at h1
      have ha : a = 9 := by 
        linarith
      simp [ha]
      <;> tauto
    · -- x = 7
      rw [show x = 7 by linarith] at h1
      have ha : a = -71 := by 
        linarith
      simp [ha]
      <;> tauto
    · -- x = -7
      rw [show x = -7 by linarith] at h1
      have ha : a = -27 := by 
        linarith
      simp [ha]
      <;> tauto
  · -- Now prove the reverse direction: each a in the set implies there's an integer root
    rintro (rfl | rfl | rfl | rfl)
    · -- a = -71, x = 7 is a root
      use 7
      norm_num
    · -- a = -27, x = -7 is a root
      use -7
      norm_num
    · -- a = -11, x = 1 is a root
      use 1
      norm_num
    · -- a = 9, x = -1 is a root
      use -1
      norm_num