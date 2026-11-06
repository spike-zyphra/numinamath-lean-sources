import Mathlib

theorem algebra_207205 : IsGreatest {a | ∃ x : ℤ, (x - a) * (x - 7) + 3 = 0} 11 := by
  constructor
  · -- First part: prove that 11 is in the set
    use 10
    norm_num
  · -- Second part: prove that 11 is the greatest
    intro a
    intro ha
    rcases ha with ⟨x, hx⟩
    have h : (x - a) * (x - 7) = -3 := by linarith
    have h1 : x - 7 ∣ -3 := by
      use (x - a)
      linarith
    have h2 : x - 7 ∣ 3 := by
      exact Int.dvd_neg.mp h1
    have h3 : (x - 7) = 1 ∨ (x - 7) = -1 ∨ (x - 7) = 3 ∨ (x - 7) = -3 := by
      have h4 : (x - 7) ∣ 3 := h2
      have h5 : (x - 7) = 1 ∨ (x - 7) = -1 ∨ (x - 7) = 3 ∨ (x - 7) = -3 := by
        have h6 : (x - 7) ≤ 3 := by
          exact Int.le_of_dvd (by norm_num) h4
        have h7 : (x - 7) ≥ -3 := by
          have h8 : (- (x - 7)) ∣ 3 := by
            exact Int.neg_dvd.2 h4
          have h9 : (- (x - 7)) ≤ 3 := by
            exact Int.le_of_dvd (by norm_num) h8
          linarith
        interval_cases (x - 7) <;> tauto
      exact h5
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- Case where x - 7 = 1, so x = 8
      have hx1 : x = 8 := by linarith
      rw [hx1] at h
      have ha1 : (8 - a) = -3 := by nlinarith
      linarith
    · -- Case where x - 7 = -1, so x = 6
      have hx1 : x = 6 := by linarith
      rw [hx1] at h
      nlinarith
    · -- Case where x - 7 = 3, so x = 10
      have hx1 : x = 10 := by linarith
      rw [hx1] at h
      nlinarith
    · -- Case where x - 7 = -3, so x = 4
      have hx1 : x = 4 := by linarith
      rw [hx1] at h
      nlinarith