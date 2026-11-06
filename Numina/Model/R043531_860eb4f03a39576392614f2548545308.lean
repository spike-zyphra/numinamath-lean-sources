import Mathlib

theorem number_theory_36754 : {n : ℤ | IsSquare (4 * n + 1) ∧ IsSquare (9 * n + 1)} = {0}:= by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume both 4n+1 and 9n+1 are squares
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    have eq1 : 4 * n + 1 = a^2 := by 
      linarith
    have eq2 : 9 * n + 1 = b^2 := by
      linarith
    have eq3 : 9 * a^2 - 4 * b^2 = 5 := by
      nlinarith
    have eq4 : (3 * a - 2 * b) * (3 * a + 2 * b) = 5 := by
      nlinarith
    have h3 : 3 * a - 2 * b = 1 ∨ 3 * a - 2 * b = 5 ∨ 3 * a - 2 * b = -1 ∨ 3 * a - 2 * b = -5 := by 
      have h4 : (3 * a - 2 * b) ∣ 5 := by
        use (3 * a + 2 * b)
        all_goals linarith
      have h5 : (3 * a - 2 * b) ≤ 5 := by
        exact Int.le_of_dvd (by norm_num) h4
      have h6 : (3 * a - 2 * b) ≥ -5 := by 
        have : - (3 * a - 2 * b) ∣ 5 := by 
          exact Int.neg_dvd.2 h4
        have : - (3 * a - 2 * b) ≤ 5 := by 
          exact Int.le_of_dvd (by norm_num) this
        omega
      interval_cases (3 * a - 2 * b) <;> try tauto
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- $3a - 2b = 1$
      have h4 : 3 * a + 2 * b = 5 := by
        nlinarith
      have ha1 : a = 1 := by
        omega
      have hn0 : n = 0 := by
        rw [ha1] at ha
        nlinarith
      exact hn0
    · -- $3a - 2b = 5$
      have h4 : 3 * a + 2 * b = 1 := by
        nlinarith
      have ha1 : a = 1 := by
        omega
      have hn0 : n = 0 := by
        rw [ha1] at ha
        nlinarith
      exact hn0
    · -- $3a - 2b = -1$
      have h4 : 3 * a + 2 * b = -5 := by
        nlinarith
      have ha1 : a = -1 := by
        omega
      have hn0 : n = 0 := by
        rw [ha1] at ha
        nlinarith
      exact hn0
    · -- $3a - 2b = -5$
      have h4 : 3 * a + 2 * b = -1 := by
        nlinarith
      have ha1 : a = -1 := by
        omega
      have hn0 : n = 0 := by
        rw [ha1] at ha
        nlinarith
      exact hn0
  · -- Assume n = 0, prove both are squares
    intro h
    rw [h]
    constructor
    · -- Show 4 * 0 + 1 is a square
      use 1
      all_goals norm_num
    · -- Show 9 * 0 + 1 is a square
      use 1
      all_goals norm_num