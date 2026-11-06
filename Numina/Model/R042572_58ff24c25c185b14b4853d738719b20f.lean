import Mathlib

theorem algebra_609431 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a + a * b + a * b * c = 11} = {(1, 1, 9), (1, 2, 4), (1, 5, 1)}:= by
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- Forward direction: if (a, b, c) is in the left side set, it's in the right side.
    rintro ⟨ha, hb, hc, h⟩
    have h1 : a ∣ 11 := by
      use 1 + b + b * c
      all_goals nlinarith
    have h2 : a = 1 ∨ a = 11 := by
      have h3 : a ≤ 11 := by
        exact Nat.le_of_dvd (by norm_num) h1
      interval_cases a <;> tauto
    rcases h2 with (h3 | h3)
    · -- Assume a = 1
      have h4 : 1 + b + b * c = 11 := by
        rw [h3] at h
        nlinarith
      have h5 : b ≤ 10 := by
        nlinarith [sq_nonneg (b : ℕ), sq_nonneg (c : ℕ), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
      interval_cases b <;> try { 
        omega 
      }
    · -- Assume a = 11
      have h4 : 1 + b + b * c = 1 := by
        rw [h3] at h
        nlinarith
      have h5 : b + b * c = 0 := by
        omega
      have h6 : b + b * c > 0 := by
        nlinarith [mul_pos hb (show 0 < c by linarith)]
      omega
  · -- Backward direction: if (a, b, c) is in the right side set, it's in the left side.
    rintro ( ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ )
    · -- First solution
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Second solution
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Third solution
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num