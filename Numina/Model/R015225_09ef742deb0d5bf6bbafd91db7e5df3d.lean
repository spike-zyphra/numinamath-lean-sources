import Mathlib

theorem algebra_10434 {A B : ℤ} (h : ∀ y, 12*y^2-65*y+42 = (A*y-14)*(B*y-3)) :
    A*B + A = 15 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  have eq6 : A * B = 12 := by
    nlinarith
  have eq7 : 3 * A + 14 * B = 65 := by
    nlinarith
  have h8 : A = 3 := by
    have eq8 : A * B = 12 := eq6
    have eq9 : 3 * A + 14 * B = 65 := eq7
    have h10 : A ∣ 12 := by
      use B
      all_goals nlinarith
    have h11 : A ≤ 12 := by
      have h12 : A ∣ 12 := h10
      have h13 : A ≤ 12 := by
        exact Int.le_of_dvd (by norm_num) h12
      linarith
    have h12 : A ≥ -12 := by
      have h13 : -A ∣ 12 := by
        exact Int.neg_dvd.2 h10
      have h14 : -A ≤ 12 := by
        exact Int.le_of_dvd (by norm_num) h13
      have h15 : -A ≥ -12 := by
        omega
      omega
    interval_cases A <;> try { 
      omega 
    }
    <;> try { 
      omega 
    }
  have h9 : B = 4 := by 
    rw [show A = 3 by exact h8] at eq6
    nlinarith
  rw [h8, h9]
  all_goals norm_num