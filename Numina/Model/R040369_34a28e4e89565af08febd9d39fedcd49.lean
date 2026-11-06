import Mathlib

theorem algebra_14334 :
    IsLeast {x | ∃ a b : ℤ, a * b = 100 ∧ x = a + b} (-101) := by
  constructor
  · -- Verify that -101 is indeed achievable with the pair (-1, -100)
    use -1, -100
    all_goals norm_num
  · -- Show there is no smaller value in the set
    intro x hx
    rcases hx with ⟨a, b, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : x < -101 := by linarith
    rw [h2] at h3
    -- Now we need to derive a contradiction for the integer pair (a, b)
    -- such that a * b = 100 and a + b < -101
    have h4 : a * b = 100 := h1
    have h5 : a + b ≤ -102 := by linarith
    have h7 : a ∣ 100 := by
      use b
      linarith
    have h8 : b ∣ 100 := by
      use a
      linarith
    have h10 : a ≤ 100 := by
      apply Int.le_of_dvd (by norm_num) h7
    have h11 : a ≥ -100 := by
      have h11 : a ∣ 100 := h7
      have h12 : -a ∣ 100 := by
        exact Int.neg_dvd.2 h11
      have h13 : -a ≤ 100 := by
        apply Int.le_of_dvd (by norm_num) h12
      linarith
    have h12 : b ≤ 100 := by
      apply Int.le_of_dvd (by norm_num) h8
    have h13 : b ≥ -100 := by
      have h13 : b ∣ 100 := h8
      have h14 : -b ∣ 100 := by
        exact Int.neg_dvd.2 h13
      have h15 : -b ≤ 100 := by
        apply Int.le_of_dvd (by norm_num) h14
      linarith
    interval_cases a <;> omega