import Mathlib

theorem inequalities_6226 : {x : ℤ | -6 < (2 * (x + 2) : ℝ) / 3 ∧ (2 * (x + 2) : ℝ) / 3 ≤ 10}.ncard = 24 := by
  have h1 : {x : ℤ | -6 < (2 * (x + 2) : ℝ) / 3 ∧ (2 * (x + 2) : ℝ) / 3 ≤ 10} = Set.Icc (-10 : ℤ) (13 : ℤ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume x is in the set
      rintro ⟨h1, h2⟩
      have h3 : (x : ℝ) > (-11 : ℝ) := by
        nlinarith
      have h4 : (x : ℝ) ≤ (13 : ℝ) := by
        nlinarith
      have hx1 : x > -11 := by
        by_contra h
        push_neg at h
        have h4' : x ≤ -11 := by omega
        have h3' : (x : ℝ) ≤ (-11 : ℝ) := by
          exact_mod_cast h4'
        linarith
      have hx2 : x ≤ 13 := by
        by_contra h
        push_neg at h
        have h5 : x ≥ 14 := by omega
        have h5' : (x : ℝ) ≥ (14 : ℝ) := by
          exact_mod_cast h5
        linarith
      constructor
      · -- Show that x ≥ -10
        omega
      · -- Show that x ≤ 13
        omega
    · -- Assume x is in the interval
      rintro ⟨h1, h2⟩
      have h3 : x ≥ -10 := by omega
      have h4 : x ≤ 13 := by omega
      have h5 : (x : ℝ) ≥ (-10 : ℝ) := by
        exact_mod_cast h3
      have h6 : (x : ℝ) ≤ (13 : ℝ) := by
        exact_mod_cast h4
      constructor
      · -- Prove first part: -6 < (2 * (x + 2) / 3)
        nlinarith
      · -- Prove second part: 2 * (x + 2) / 3 ≤ 10
        nlinarith
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }