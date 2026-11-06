import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_139237 (f : ℝ → ℝ → ℝ)
  (h₀ : f = λ x y => 4 * x ^ 2 + y ^ 2 - 16 * x - 4 * y + 20)
  (D : Set (ℝ × ℝ))
  (hD : D = {(x, y) | 0 ≤ x ∧ x - 2 * y ≤ 0 ∧ x + y - 6 ≤ 0}) :
  IsLeast {z | ∃ x y, z = f x y ∧ (x, y) ∈ D} 0 ∧
  IsGreatest {z | ∃ x y, z = f x y ∧ (x, y) ∈ D} 32 := by

  constructor
  · -- Show 0 is the least element of the set
    constructor
    · -- Show 0 is in the set
      use 2, 2
      constructor
      · -- Show z = f 2 2
        rw [h₀]
        norm_num
      · -- Show (2, 2) ∈ D
        rw [hD]
        exact ⟨by norm_num, by norm_num, by norm_num⟩
    · -- Show no element less than 0 is in the set
      intro z h
      rcases h with ⟨x, y, hz, hP⟩
      rw [h₀] at hz
      simp at hz
      have h1 : 0 ≤ x := by
        have h1 : (x, y) ∈ D := hP
        rw [hD] at h1
        exact h1.1
      have h2 : x - 2 * y ≤ 0 := by
        have h1 : (x, y) ∈ D := hP
        rw [hD] at h1
        exact h1.2.1
      have h3 : x + y - 6 ≤ 0 := by
        have h1 : (x, y) ∈ D := hP
        rw [hD] at h1
        exact h1.2.2
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2)]
  · -- Show 32 is the greatest element of the set
    constructor
    · -- Show 32 is in the set
      use 0, 6
      constructor
      · -- Show z = f 0 6
        rw [h₀]
        norm_num
      · -- Show (0, 6) ∈ D
        rw [hD]
        exact ⟨by norm_num, by norm_num, by norm_num⟩
    · -- Show no element greater than 32 is in the set
      intro z h
      rcases h with ⟨x, y, hz, hP⟩
      rw [h₀] at hz
      simp at hz
      have h1 : 0 ≤ x := by
        have h1 : (x, y) ∈ D := hP
        rw [hD] at h1
        exact h1.1
      have h2 : x - 2 * y ≤ 0 := by
        have h1 : (x, y) ∈ D := hP
        rw [hD] at h1
        exact h1.2.1
      have h3 : x + y - 6 ≤ 0 := by
        have h1 : (x, y) ∈ D := hP
        rw [hD] at h1
        exact h1.2.2
      nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 6), sq_nonneg (x - 4), sq_nonneg (y - 2)]