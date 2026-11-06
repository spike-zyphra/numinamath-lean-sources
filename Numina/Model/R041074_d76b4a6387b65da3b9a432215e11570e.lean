import Mathlib

theorem number_theory_232376 :
    {d : ℤ | d > 0 ∧ ∃ a : ℤ, d ∣ (35*a + 57) ∧ d ∣ (45*a + 76)} = 
    {1, 19} := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, prove the forward direction: if $d > 0$ and there exists $a$ such that $d$ divides both $35a + 57$ and $45a + 76$, then $d$ must be 1 or 19.
    rintro ⟨hd_pos, a, h1, h2⟩
    have h3 : d ∣ 19 := by
      have h4 : d ∣ (35 * a + 57) := h1
      have h5 : d ∣ (45 * a + 76) := h2
      have h6 : d ∣ (9 * (35 * a + 57) - 7 * (45 * a + 76)) := by
        apply Dvd.dvd.sub
        . apply Dvd.dvd.mul_left
          exact h4
        . apply Dvd.dvd.mul_left
          exact h5
      have h7 : (9 * (35 * a + 57) - 7 * (45 * a + 76) : ℤ) = -19 := by
        ring_nf
      rw [h7] at h6
      have h8 : d ∣ 19 := by
        exact Int.dvd_neg.mp h6
      exact h8
    have h4 : d = 1 ∨ d = 19 := by
      have h5 : d ∣ 19 := h3
      have h6 : d > 0 := hd_pos
      have h7 : d ≤ 19 := by
        exact Int.le_of_dvd (by norm_num) h5
      interval_cases d <;> tauto
    tauto
  · -- Now prove the reverse direction: any 1 or 19 is in the set
    rintro (h | h)
    · -- d = 1
      rw [h]
      constructor
      · norm_num
      · -- exists a
        use 0
        all_goals norm_num
    · -- d = 19
      rw [h]
      constructor
      · norm_num
      · -- exists a
        use 0
        all_goals norm_num