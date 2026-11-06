import Mathlib

theorem algebra_327520 : {(m, n) : ℤ × ℤ | m^2 - n^2 + 3 * m - 7 * n - 2 = 0}.ncard = 4 := by
  have h1 : {(m, n) : ℤ × ℤ | m^2 - n^2 + 3 * m - 7 * n - 2 = 0} = { 
      (2, 1), (-5, 1), (-5, -8), (2, -8)
    } := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- Assume h: m^2 - n^2 + 3 * m - 7 * n - 2 = 0, prove ( (m, n) ∈ { (2, 1), (-5, 1), (-5, -8), (2, -8) } )
      rintro H
      have eq1 : (n - m + 2) * (n + m + 5) = 8 := by
        nlinarith
      have h2 : n - m + 2 ∣ 8 := by 
        use n + m + 5
        all_goals nlinarith
      have h3 : n - m + 2 ≥ -8 := by
        have h4 : n - m + 2 ∣ 8 := h2
        have : n - m + 2 ≤ 8 := by
          apply Int.le_of_dvd (by norm_num) h4
        have : n - m + 2 ≥ -8 := by
          have h5 : -(n - m + 2) ∣ 8 := by 
            exact Int.neg_dvd.2 h4
          have h6 : -(n - m + 2) ≤ 8 := by
            apply Int.le_of_dvd (by norm_num) h5
          omega
        omega
      have h4 : n - m + 2 ≤ 8 := by
        have h5 : n - m + 2 ∣ 8 := h2
        have : n - m + 2 ≤ 8 := by
          apply Int.le_of_dvd (by norm_num) h5
        omega
      interval_cases h : n - m + 2 <;> omega
    · -- Show that (2, 1), (-5, 1), (-5, -8), (2, -8) satisfy the equation.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }