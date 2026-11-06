import Mathlib

theorem algebra_13522 (s : Set ℤ) (hs : s = {y : ℤ | ∃ x : ℤ, 0 < x ∧ 0 < y ∧ 3 * x ^ 2 + 2 * x + 92 = 3 * y ^ 2}) :
    ∑ᶠ y ∈ s, y = 16 := by
  have h4 : s = {6, 10} := by
    ext y
    simp [hs]
    constructor
    · -- If $y \in s$, then $y \in \{6, 10\}$.
      rintro ⟨x, hx, hy, heq⟩
      have h2 : (3 * y : ℤ) ^ 2 - (3 * x + 1)^2 = 275 := by
        nlinarith
      have h3 : (3 * y - (3 * x + 1)) * (3 * y + (3 * x + 1)) = 275 := by
        nlinarith
      have h4 : (3 * y - (3 * x + 1)) ∣ 275 := by
        use (3 * y + (3 * x + 1))
        all_goals linarith
      have h5 : (3 * y - (3 * x + 1)) ≥ -275 := by
        have h41 : -(3 * y - (3 * x + 1)) ∣ 275 := by
          exact Int.neg_dvd.2 h4
        have h42 : -(3 * y - (3 * x + 1)) ≤ 275 := by
          exact Int.le_of_dvd (by norm_num) h41
        linarith
      have h6 : (3 * y - (3 * x + 1)) ≤ 275 := by
        exact Int.le_of_dvd (by norm_num) h4
      interval_cases h7 : (3 * y - (3 * x + 1)) <;> omega
    · -- If $y \in \{ 6, 10 \}$, then $y \in s$.
      rintro (rfl | rfl)
      · -- Check $y = 6$.
        use 2
        all_goals norm_num
      · -- Check $y = 10$.
        use 8
        all_goals norm_num
  rw [h4]
  rw [finsum_mem_pair]
  all_goals norm_num
  all_goals norm_num