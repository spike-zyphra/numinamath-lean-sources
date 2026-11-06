import Mathlib

theorem algebra_10639 {m n : ℤ} :
    { (m, n) : ℤ × ℤ | m > 0 ∧ n > 0 ∧ 
    14 * m * n = 55 - 7 * m - 2 * n} = {(1,3)}:= by
  ext ⟨m, n⟩
  simp
  constructor
  · -- If (m, n) satisfy the equation, then (m, n) = (1, 3)
    rintro ⟨hm, hn, h⟩
    have h1 : (7 * m + 1) * (2 * n + 1) = 56 := by 
      nlinarith
    have h2 : (7 * m + 1) ∣ 56 := by
      use (2 * n + 1)
      linarith
    have h3 : (7 * m + 1) ≤ 56 := by
      exact Int.le_of_dvd (by norm_num) h2
    have h4 : (7 * m + 1) ≥ 8 := by 
      omega
    have h5 : (7 * m + 1) = 8 ∨ (7 * m + 1) = 14 ∨ (7 * m + 1) = 28 ∨ (7 * m + 1) = 56 := by
      interval_cases h6 : (7 * m + 1) <;> omega
    rcases h5 with (h5 | h5 | h5 | h5)
    · -- $7 * m + 1 = 8$
      have hm1 : m = 1 := by 
        omega
      have hn1 : n = 3 := by 
        nlinarith
      simp [hm1, hn1]
    · -- $7 * m + 1 = 14$
      exfalso 
      omega
    · -- $7 * m + 1 = 28$
      exfalso 
      omega
    · -- $7 * m + 1 = 56$
      exfalso 
      omega
  · -- (m, n) = (1, 3) satisfy the equation
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num