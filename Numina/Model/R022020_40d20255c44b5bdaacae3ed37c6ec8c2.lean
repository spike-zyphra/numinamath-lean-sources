import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_192521 (a : ℝ) (ha : a > 0) :
    {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} =
    {2, 3} ∨ {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} =
    {3, 4} → 2.375 ≤ a ∧ a ≤ 2.8 := by
  intro h
  rcases h with (h | h)
  · -- {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} = {2, 3}
    have h2 : (2 : ℤ) ∈ {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} := by
      rw [h]
      simp
    have h3 : (3 : ℤ) ∈ {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} := by
      rw [h]
      simp
    have h4 : (4 : ℤ) ∉ {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} := by
      rw [h]
      simp
    simp at h2 h3 h4
    -- For 3: 3^2 - 2 a * 3 + 3 ≤ 0 ⇒ 9 - 6a + 3 ≤ 0 ⇒ 12 ≤ 6a ⇒ a ≥ 2
    -- For 4: 4^2 - 2 a * 4 + 3 > 0 ⇒ 16 - 8a + 3 > 0 ⇒ 19 > 8a ⇒ a < 19/8 = 2.375
    -- For 2: 2^2 - 2 a * 2 + 3 ≤ 0 ⇒ 4 - 4a + 3 ≤ 0 ⇒ 7 ≤ 4a ⇒ a ≥ 1.75
    -- Contradicts as 4 > 0 so it should be in A
    -- This case is impossible as {2,3} can't be the intersection
    all_goals norm_cast at h2 h3 h4 ⊢
    all_goals nlinarith
  · -- {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} = {3, 4}
    have h3 : (3 : ℤ) ∈ {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} := by
      rw [h]
      simp
    have h4 : (4 : ℤ) ∈ {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} := by
      rw [h]
      simp
    have h5 : (5 : ℤ) ∉ {x : ℤ | x^2 + x - 6 > 0} ∩ {x : ℤ | x^2 - 2 * a * x + 3 ≤ 0} := by
      rw [h]
      simp
    simp at h3 h4 h5
    -- For 3: 3^2 - 2 a * 3 + 3 ≤ 0 ⇒ 9 - 6a + 3 ≤ 0 ⇒ 12 ≤ 6a ⇒ a ≥ 2
    -- For 4: 4^2 - 2 a * 4 + 3 ≤ 0 ⇒ 16 - 8a + 3 ≤ 0 ⇒ 19 ≤ 8a ⇒ a ≥ 19/8 = 2.375
    -- For 5: 5^2 - 2 a * 5 + 3 > 0 ⇒ 25 - 10a + 3 > 0 ⇒ 28 > 10a ⇒ a < 2.8
    -- Combining: 2.375 ≤ a ≤ 2.8
    -- This is the correct case, and it leads to the required inequality
    have h3' : (3 : ℝ)^2 - 2 * a * (3 : ℝ) + 3 ≤ 0 := by
      norm_cast at h3 ⊢
      all_goals nlinarith
    have h4' : (4 : ℝ)^2 - 2 * a * (4 : ℝ) + 3 ≤ 0 := by
      norm_cast at h4 ⊢
      all_goals nlinarith
    have h5' : (5 : ℝ)^2 - 2 * a * (5 : ℝ) + 3 > 0 := by
      norm_cast at h5 ⊢
      all_goals nlinarith
    constructor
    · -- 2.375 ≤ a
      nlinarith
    · -- a ≤ 2.8
      nlinarith