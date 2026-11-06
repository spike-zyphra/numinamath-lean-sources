import Mathlib

theorem algebra_184166 :
    {n : ℤ | (n^2 - 4) ≠ 0 ∧ (n^2 + 2 * n - 8) % (n^2 - 4) = 0} = {n : ℤ | n = -1 ∨ n=-3 ∨ n=0 ∨ n = -4} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume n in left side, prove in right side
    rintro ⟨h1, h2⟩
    have h3 : (n^2 - 4) ∣ (n^2 + 2 * n - 8) := by
      exact Int.dvd_of_emod_eq_zero h2
    have h4 : n ≠ 2 := by
      by_contra h
      have h5 : n^2 - 4 = 0 := by
        rw [h]
        norm_num
      tauto
    have h5 : n ≠ -2 := by
      by_contra h
      have h6 : n^2 - 4 = 0 := by
        rw [h]
        norm_num
      tauto
    -- Factor the numerator and denominator.
    -- The numerator is n^2 + 2n - 8 = (n + 4)(n - 2).
    -- The denominator is n^2 - 4 = (n - 2)(n + 2).
    -- Assume f : (n - 2) * (n + 2) | (n + 4) * (n - 2)
    rw [show n^2 - 4 = (n - 2) * (n + 2) by ring] at h3
    rw [show n^2 + 2 * n - 8 = (n + 4) * (n - 2) by ring] at h3
    -- From `h3 : (n - 2) * (n + 2) | (n + 4) * (n - 2)`, given nne 2
    -- We can cancel `n - 2` from both sides.
    -- Because n ne 2, so n - 2 ne 0, then it is possible to cancel.
    have h10 : (n + 2) ∣ (n + 4) := by
      have h11 : (n - 2) * (n + 2) ∣ (n + 4) * (n - 2) := h3
      have h12 : n - 2 ≠ 0 := by
        intro h13
        apply h4
        omega
      obtain ⟨k, hk⟩ := h11
      have h14 : (n + 4) * (n - 2) = (n - 2) * (n + 2) * k := by
        nlinarith
      have h115 : (n + 4) = (n + 2) * k := by
        apply (mul_left_inj' h12).mp
        linarith
      use k
      all_goals linarith
      all_goals linarith
    -- Now we need that `n + 2` divides `n + 4`.
    -- That implies that `n + 2` divides `n + 4 - (n + 2) = 2`.
    have h12 : n + 2 ∣ 2 := by
      have h14 : n + 2 ∣ n + 4 := h10
      have h15 : n + 2 ∣ (n + 4 - (n + 2)) := by
        apply Dvd.dvd.sub
        · exact h14
        · exact dvd_refl (n + 2)
      have h16 : (n + 4 - (n + 2)) = 2 := by
        linarith
      rw [h16] at h15
      exact h15
    -- From `n + 2` divides `2`, so `n + 2` can be 1,2, -1, -2.
    have h13 : n + 2 ∣ 2 := h12
    have h14 : n + 2 ≤ 2 := by
      apply Int.le_of_dvd (by norm_num) h13
    have h15 : n + 2 ≥ -2 := by
      have h16 : (- (n + 2)) ∣ 2 := by
        exact Int.neg_dvd.2 h13
      have h17 : - (n + 2) ≤ 2 := by
        apply Int.le_of_dvd (by norm_num) h16
      omega
    have h16 : n ≤ 4 := by
      omega
    have h17 : n ≥ -4 := by
      omega
    interval_cases n <;> norm_num at *
  · -- Assume in right side, prove left side
    rintro (h | h | h | h)
    · -- n = -1
      rw [h]
      constructor
      · norm_num
      · norm_num
    · -- n = -3
      rw [h]
      constructor
      · norm_num
      · norm_num
    · -- n = 0
      rw [h]
      constructor
      · norm_num
      · norm_num
    · -- n = -4
      rw [h]
      constructor
      · norm_num
      · norm_num