import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303715 (f : ℝ → ℝ → ℝ) (hf : f = λ x y => x^2 / 4 + y^2)
  (g : ℝ → ℝ → ℝ) (hg : g = λ x y => x - y) :
  IsGreatest {z | ∃ x y, z = g x y ∧ f x y ≤ 1} (Real.sqrt 5) ∧
  IsLeast {z | ∃ x y, z = g x y ∧ f x y ≤ 1} (-Real.sqrt 5) := by 
  constructor
  · -- Show that sqrt5 is greatest in the set.
    constructor 
    · -- Show that sqrt5 is in the set.
      use (4 * Real.sqrt 5) / 5, (- Real.sqrt 5) / 5 
      constructor
      · -- Show that z = g x y.
        rw [hg]
        field_simp
        <;> ring_nf <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
      · -- Show that f x y ≤ 1
        rw [hf]
        simp 
        have h1 : (Real.sqrt 5) ^ 2 = 5 := by 
          norm_num [Real.sq_sqrt]
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0)]
    · -- Show that for all z in the set, z ≤ sqrt5
      intro z hz 
      rcases hz with ⟨x, y, hz_eq, hz_le⟩
      have h1 : z = x - y := by
        rw [hg] at hz_eq 
        simpa using hz_eq
      have h5 : f x y ≤ 1 := hz_le 
      have h6 : f x y = x ^ 2 / 4 + y ^ 2 := by 
        rw [hf]
      have h7 : x ^ 2 / 4 + y ^ 2 ≤ 1 := by 
        linarith [h5, h6]
      have h8 : (x - y) ≤ Real.sqrt 5 := by 
        have h9 : (x - y) ^ 2 ≤ (5 : ℝ) := by
          nlinarith [sq_nonneg ((x / 2) - (2 * y)), sq_nonneg ((x / 2) + y * 2), sq_nonneg (x - 4 * y), sq_nonneg ((x + 4 * y)), Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0)]
        have h10 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5 
        have h11 : (x - y) ^ 2 ≤ (Real.sqrt 5) ^ 2 := by
          nlinarith [h9, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0)]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0)]
      linarith [h1, h8]
  · -- Show that -sqrt5 is the least in the set.
    constructor 
    · -- Show that -sqrt5 is in the set.
      use (-4 * Real.sqrt 5) / 5, (Real.sqrt 5) / 5 
      constructor
      · -- Show that z = g x y.
        rw [hg]
        field_simp 
        <;> ring_nf <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
      · -- Show that f x y ≤ 1
        rw [hf]
        simp 
        have h1 : (Real.sqrt 5) ^ 2 = 5 := by 
          norm_num [Real.sq_sqrt] 
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0)]
    · -- Show that for all z in the set, -sqrt5 ≤ z
      intro z hz 
      rcases hz with ⟨x, y, hz_eq, hz_le⟩
      have h1 : z = x - y := by
        rw [hg] at hz_eq 
        simpa using hz_eq
      have h5 : f x y ≤ 1 := hz_le 
      have h6 : f x y = x ^ 2 / 4 + y ^ 2 := by 
        rw [hf]
      have h7 : x ^ 2 / 4 + y ^ 2 ≤ 1 := by 
        linarith [h5, h6]
      have h11 : -Real.sqrt 5 ≤ (x - y) := by 
        have h9 : (x - y) ^ 2 ≤ (5 : ℝ) := by
          nlinarith [sq_nonneg ((x / 2) - (2 * y)), sq_nonneg ((x / 2) + y * 2), sq_nonneg (x - 4 * y), sq_nonneg ((x + 4 * y)), Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0)]
        have h10 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
        have h12 : (x - y) ^ 2 ≤ (Real.sqrt 5) ^ 2 := by
          nlinarith [h9, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0)]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0)]
      linarith [h1, h11]