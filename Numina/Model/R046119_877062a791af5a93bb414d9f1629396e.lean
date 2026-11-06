import Mathlib

theorem algebra_14437 : IsGreatest {x : ℤ | x - 3 ≠ 0 ∧ ∃ k : ℤ, (x ^ 2 + 2 * x + 5) / (x - 3 : ℚ) = k} 23 := by
  constructor
  · -- First part: Show that 23 is in the set
    constructor
    · norm_num
    · use 29
      norm_num
  · -- Second part: Show that no integer greater than 23 is in the set
    intro x ⟨hx1, ⟨k, hk⟩⟩
    have h1 : x - 3 ≠ 0 := hx1
    have h2 : (x ^ 2 + 2 * x + 5 : ℚ) / (x - 3 : ℚ) = (k : ℚ) := by
      simpa using hk
    have h4 : (x : ℚ) - 3 ≠ 0 := by
      exact_mod_cast h1
    have h5 : (x ^ 2 + 2 * x + 5 : ℚ) = k * (x - 3 : ℚ) := by
      field_simp [h4] at h2 ⊢
      linarith
    have h6 : x ^ 2 + 2 * x + 5 = k * (x - 3) := by
      exact_mod_cast h5
    have h7 : x - 3 ∣ 20 := by
      use (k - (x + 5))
      nlinarith
    by_contra h
    push_neg at h
    have h8 : x > 23 := h
    have h9 : x - 3 > 20 := by
      omega
    have h10 : x - 3 > 0 := by nlinarith
    have h11 : x - 3 ≤ 20 := by
      apply Int.le_of_dvd (by norm_num) h7
    linarith