import Mathlib

/- A rectangular band formation is a formation with $m$ band members in each of $r$ rows, where $m$ and $r$ are integers. A particular band has less than 100 band members. The director arranges them in a rectangular formation and finds that he has two members left over. If he increases the number of members in each row by 1 and reduces the number of rows by 2, there are exactly enough places in the new formation for each band member. What is the largest number of members the band could have? -/
theorem algebra_10173 : IsGreatest { m : ℕ | m < 100 ∧ ∃ r x, r > 2 ∧ x > 1 ∧ r * x + 2 = m ∧ (r - 2) * (x + 1) = m } 98 := by
  -- Two goals to prove:
  -- 1. 98 is a possible number of band members
  -- 2. There is no number of band members greater than 98 that satisfies the conditions, we only need to prove that 99 is not a possible number of band members
  constructor
  . -- 98 is a possible number of band members
    -- Set r = 16 and x = 6
    refine ⟨by simp, ?_⟩
    use 16, 6
    simp
  . intro m ⟨hm, r, x, hr, hx, h1, h2⟩
    zify at h1 h2
    simp [show r ≥ 2 from le_of_lt hr] at h2
    -- Subtract h1 and h2, we get r = 2x + 4
    have H : (r : ℤ) = 2 * x + 4 := by
      calc _ = ((r - 2) * (x + 1) - (r * x + 2) + 2 * x + 4 : ℤ) := by ring
           _ = _ := by simp [h1, h2]
    norm_cast at H h1
    -- Thus m = 2 * ((x + 2) * x + 1) is even
    have h3 : m = 2 * ((x + 2) * x + 1) := by
      rw [← h1, H]
      ring
    have mEven : m % 2 = 0 := by
      rw [h3]
      exact Nat.mul_mod_right _ _
    -- If m > 98, then m = 99
    by_contra!
    interval_cases m
    -- But 99 is not even
    simp at mEven
