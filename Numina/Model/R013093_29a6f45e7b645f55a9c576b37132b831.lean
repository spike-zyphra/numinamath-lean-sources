import Mathlib

theorem algebra_18910 (a : ℕ → ℤ) (ha : ∀ n, a n = 1000 - 13 * n) :
    IsLeast {x | ∃ n, x = a n ∧ x > 0} 12 := by
  constructor
  · -- Show that 12 is in the set: existence
    use 76
    norm_num [ha]
    all_goals omega
  · -- Show that 12 is the minimum
    intro x hx
    rcases hx with ⟨n, hn1, hn2⟩
    have h1 : x = 1000 - 13 * n := by
      rw [hn1]
      rw [ha n]
      <;> omega
    have h2 : (1000 - 13 * n : ℤ) > 0 := by
      linarith [h1, hn2]
    have h3 : n ≤ 76 := by
      by_contra h
      push_neg at h
      have h4 : n ≥ 77 := by omega
      have h5 : (13 * (n : ℤ) ) ≥ (13 * 77 : ℤ) := by
        apply mul_le_mul_of_nonneg_left
        omega
        norm_num
        all_goals omega
      have h6 : (1000 : ℤ) - (13 * (n : ℤ)) ≤ (1000 : ℤ) - (13 * 77 : ℤ) := by linarith
      have h7 : (1000 : ℤ) - (13 * 77 : ℤ) ≤ 0 := by
        norm_num
      have h8 : (1000 - 13 * n : ℤ) ≤ 0 := by linarith [h6, h7]
      linarith [show (1000 - 13 * n : ℤ) > 0 from by linarith [h2]]
    have h4 : x ≥ 12 := by
      rw [h1]
      omega
    linarith