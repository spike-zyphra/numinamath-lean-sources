import Mathlib

/- How many three digit numbers are there such that the digits are non-zero, the tens digit is a multiple of the hundreds digit, the units digit is a multiple of the tens digit, and none of the digits are the same? -/
theorem number_theory_23090 :
    Set.ncard { 100 * x + 10 * y + z | (x : ℕ) (y : ℕ) (z : ℕ) (_ : 1 ≤ x) (_ : x ≤ 9) (_ : 1 ≤ y) (_ : y ≤ 9) (_ : 1 ≤ z) (_ : z ≤ 9) (_ : x ∣ y) (_ : y ∣ z) (_ : x ≠ y ∧ y ≠ z ∧ x ≠ z) } = 7 := by
  -- We find all the numbers that satisfy the conditions and count them
  suffices H : { 100 * x + 10 * y + z | (x : ℕ) (y : ℕ) (z : ℕ) (_ : 1 ≤ x) (_ : x ≤ 9) (_ : 1 ≤ y) (_ : y ≤ 9) (_ : 1 ≤ z) (_ : z ≤ 9) (_ : x ∣ y) (_ : y ∣ z) (_ : x ≠ y ∧ y ≠ z ∧ x ≠ z) } = { 124, 126, 128, 136, 139, 148, 248 } by
    -- Count the elements of the set
    rw [H,
        show ({ 124, 126, 128, 136, 139, 148, 248 } : Set ℕ) = ({ 124, 126, 128, 136, 139, 148, 248 } : Finset ℕ) by simp,
        Set.ncard_coe_Finset]
    simp
  -- We prove the equivalence by double inclusion
  ext a
  simp
  constructor
  . -- First, we prove that the conditions imply that a is in the set
    rintro ⟨x, y, z, ⟨h1, h2, h3⟩, h4, h5, h6, h7, h8, h9, h10, h11, rfl⟩
    -- We know that x divides y and y divides z, get the quotients
    rcases h5 with ⟨n1, hn1⟩
    rcases h4 with ⟨n2, hn2⟩
    -- y ≥ 2x and z ≥ 2y, because the digits are non-zero and they are all different
    have k1 : y ≥ 2 * x := by
      clear * - h11 n1 hn1 h1 h9
      suffices n1 ≥ 2 by nlinarith only [h11, hn1, this]
      by_contra!
      interval_cases n1
      . simp at hn1
        subst hn1
        simp at h9
      . simp at hn1
        exact h1 hn1.symm
    have k2 : z ≥ 2 * y := by
      clear * - h2 n2 hn2 h7 h9
      suffices n2 ≥ 2 by nlinarith only [h9, hn2, this]
      by_contra!
      interval_cases n2
      . simp at hn2
        subst hn2
        simp at h7
      . simp at hn2
        exact h2 hn2.symm
    -- z ≥ 4x, and thus x < 3
    have k3 : x < 3 := by linarith only [h6, k1, k2]
    -- x = 1 or x = 2
    interval_cases x
    . -- x = 1
      -- 2y ≤ z ≤ 9, y < 5
      have k4 : y < 5 := by linarith only [h6, k2]
      have k5 : n2 ≥ 2 := by nlinarith only [hn2, k2, h9]
      -- y = 2 or y = 3 or y = 4
      interval_cases y
      . -- y = 2
        have k6 : n2 < 5 := by linarith only [hn2, h6]
        -- n2 = 2, 3 or 4
        interval_cases n2
        -- Any of the cases is a solution
        all_goals
          subst hn2
          simp
      . -- y = 3
        have k6 : n2 < 4 := by linarith only [hn2, h6]
        -- n2 = 2 or 3
        interval_cases n2
        -- Both cases are solutions
        all_goals
          subst hn2
          simp
      . -- y = 4
        have k6 : n2 < 3 := by linarith only [hn2, h6]
        -- n2 = 2
        interval_cases n2
        -- This case is a solution
        subst hn2
        simp
    . -- x = 2
      subst hn1
      -- n1 can only be 2
      have k4 : n1 ≥ 2 := by linarith only [k1]
      have k5 : n1 < 3 := by linarith only [k2, h6]
      interval_cases n1
      -- n2 can only be 2
      subst hn2
      have k6 : n2 ≥ 2 := by linarith only [k2]
      have k7 : n2 < 3 := by linarith only [h6]
      interval_cases n2
      -- This case is a solution
      simp
  . -- Just prove that the elements of the set satisfy the conditions
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    . use 1, 2, 4
      simp
      use 2
    . use 1, 2, 6
      simp
      use 3
    . use 1, 2, 8
      simp
      use 4
    . use 1, 3, 6
      simp
      use 2
    . use 1, 3, 9
      simp
      use 3
    . use 1, 4, 8
      simp
      use 2
    . use 2, 4, 8
      simp
      constructor
      . use 2
      . use 2
