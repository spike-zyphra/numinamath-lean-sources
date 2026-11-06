import Mathlib

/-The product of three different positive integers is 144 .
What is the maximum possible sum of these three integers?
(A) 20 (B) 75 (C) 146 (D) 52 (E) 29-/

theorem number_theory_282640:
  IsGreatest {k: ℕ | ∃ a b c: ℕ, 0 < a ∧ a < b ∧ b < c ∧ a * b * c = 144 ∧ k = a + b + c} 75 := by

  constructor

  -- the forward direction
  .
    simp
    use 1
    norm_num
    use 2
    norm_num
    use 72
    norm_num

  -- the reverse direction
  .
    intro k h
    simp at h
    obtain ⟨a, ha, b, hb, c, hc, h, hk⟩ := h
    simp [hk]
    clear hk

    -- prove by contradiction
    by_contra! l

    -- then we must have 25 < c
    have u: 25 < c := by omega

    --we note that c is a divisor of 144
    have d: c ∈ Nat.divisors 144 := by
      simp
      rw [← h]
      simp
    rw [show Nat.divisors 144 = {1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} by rfl] at d
    simp at d
    rcases d with d | d | d | d | d | d | d | d | d | d | d | d | d | d | d
    all_goals simp [d] at u
    -- it remains to check c = 36, 48, 72, 144

    -- c = 36
    .
      simp [d] at *
      replace h: a * b = 4 := by omega
      replace l: 40 ≤ a + b := by omega
      nlinarith

    -- c = 48
    .
      simp [d] at *
      replace h: a * b = 3 := by omega
      replace l: 10 < a + b := by omega
      nlinarith

    -- c = 72
    .
      simp [d] at *
      replace h: a * b = 2 := by omega
      replace l: 3 < a + b := by omega
      nlinarith

    -- c = 144
    .
      simp [d] at *
      replace h: a * b = 1 := by omega
      replace l: 2 ≤ a + b := by omega
      nlinarith