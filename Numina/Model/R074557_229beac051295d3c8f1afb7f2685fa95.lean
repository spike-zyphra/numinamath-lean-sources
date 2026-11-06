import Mathlib

theorem algebra_2251 : {k : ℤ | ∃ x : ℤ, (k - 1999) * x = 2001 - 2000 * x}.encard = 16 := by

  have h1 : {k : ℤ | ∃ x : ℤ, (k - 1999) * x = 2001 - 2000 * x} = {k : ℤ | k + 1 ∣ 2001} := by
    ext k
    simp only [Set.mem_setOf_eq]

    constructor
    · -- Assume there exists an integer x such that (k - 1999) * x = 2001 - 2000 * x
      rintro ⟨x, hx⟩
      -- Show that k + 1 divides 2001
      use x
      linarith
    · -- Assume k + 1 divides 2001
      rintro ⟨x, hx⟩
      -- Show there exists an integer x such that (k - 1999) * x = 2001 - 2000 * x
      use x
      linarith

  rw [h1]

  have h2 : {k : ℤ | k + 1 ∣ 2001} = {-2002, -668, -88, -70, -30, -24, -4, -2, 0, 2, 22, 28, 68, 86, 666, 2000} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume k + 1 divides 2001
      intro h
      have h3 : k + 1 ∣ 2001 := h
      have h4 : k + 1 ≤ 2001 := by
        apply Int.le_of_dvd (by norm_num) h3
      have h5 : k + 1 ≥ -2001 := by
        have h6 : -(k + 1) ∣ 2001 := by
          exact Int.neg_dvd.2 h3
        have h7 : -(k + 1) ≤ 2001 := by
          apply Int.le_of_dvd (by norm_num) h6
        linarith
      have h8 : k ≤ 2000 := by linarith
      have h9 : k ≥ -2002 := by linarith
      interval_cases k <;> tauto
    · -- Show that these elements indeed satisfy k + 1 divides 2001
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num

  rw [h2]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl