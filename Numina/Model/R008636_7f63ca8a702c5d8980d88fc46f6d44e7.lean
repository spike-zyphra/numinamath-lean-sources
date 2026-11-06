import Mathlib

theorem algebra_21322 : IsGreatest {c : ℝ | (c ^ 2 + 6 * c - 27) / (c - 3) + 2 * c = 23 ∧ c ≠ 3} (14 / 3) := by 
  constructor
  · -- First part: Show that 14/3 is in the set
    constructor
    · -- Verify the equation
      norm_num
    · -- Show that 14/3 ≠ 3
      norm_num
  · -- Second part: Show that if c is in the set, then c ≤ 14/3
    intro c hc
    rcases hc with ⟨hc_eq, hc_ne⟩
    have h1 : (c ^ 2 + 6 * c - 27) / (c - 3) = c + 9 := by
      have h2 : c - 3 ≠ 0 := by
        intro h3
        apply hc_ne
        linarith
      field_simp [h2]
      ring
    rw [h1] at hc_eq
    have hc_eq2 : 3 * c = 14 := by 
      linarith 
    have hc_eq3 : c = 14 / 3 := by 
      linarith
    linarith [hc_eq3]