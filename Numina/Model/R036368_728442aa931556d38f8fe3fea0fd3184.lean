import Mathlib

theorem algebra_131616 (n : ℤ) :
    (∃ x : ℤ, x^2 + n * x + n + 5 = 0) ↔ n = -5 ∨ n = -3 ∨ n = 7 ∨ n = 9 := by
  constructor
  · -- Assume there exists an integer x with x^2 + n * x + n + 5 = 0; prove n ∈ {-5, -3, 7, 9}
    rintro ⟨x, hx⟩
    have h1 : x^2 + n * x + n + 5 = 0 := hx
    have h3 : (2 * x + n)^2 = n^2 - 4 * n - 20 := by
      nlinarith
    have h4 : (n - 2)^2 - (2 * x + n)^2 = 24 := by
      nlinarith [h3]
    have h5 : (n - 2 - (2 * x + n)) * (n - 2 + (2 * x + n)) = 24 := by
      nlinarith [h4]
    have h6 : n - 2 - (2 * x + n) ∣ 24 := by
      use n - 2 + (2 * x + n)
      nlinarith [h5]
    have h7 : n - 2 - (2 * x + n) ≤ 24 := by
      apply Int.le_of_dvd (by norm_num) h6
    have h8 : n - 2 - (2 * x + n) ≥ -24 := by
      have h9 : -(n - 2 - (2 * x + n)) ∣ 24 := by
        exact Int.neg_dvd.2 h6
      have h10 : -(n - 2 - (2 * x + n)) ≤ 24 := by
        apply Int.le_of_dvd (by norm_num) h9
      linarith
    interval_cases h : n - 2 - (2 * x + n) <;> omega
  · -- Assume n ∈ {-5, -3, 7, 9}, prove there exists an integer x satisfying the equation
    rintro (h | h | h | h)
    · -- n = -5
      rw [h]
      use 0
      norm_num
    · -- n = -3
      rw [h]
      use 1
      norm_num
    · -- n = 7
      rw [h]
      use -3
      norm_num
    · -- n = 9
      rw [h]
      use -2
      norm_num