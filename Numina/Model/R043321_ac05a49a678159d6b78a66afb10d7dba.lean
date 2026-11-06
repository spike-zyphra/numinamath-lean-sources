import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_119917 {A : Set ℂ} (hA : A = {z | abs z = 1}) :
    (1 / 2 - Real.sqrt 3 / 2 * .I : ℂ) ^ 2013 ∈ A ∧
    ∀ z1 z2 : ℂ, z1 ∈ A → z2 ∈ A → z1 * z2 ∈ A ∧
    ∃ z1 z2 z3 : ℂ, z1 ∈ A ∧ z2 ∈ A ∧ z3 ∈ A ∧ z1 + z2 + z3 = 3 := by
  constructor
  · -- Show that ((1/2) - (√3/2)i)^2013 ∈ A
    rw [hA]
    have h1 : abs ((1 / 2 - Real.sqrt 3 / 2 * Complex.I : ℂ) ) = 1 := by
      simp [Complex.abs, Complex.normSq]
      ring_nf
      <;> norm_num [Real.sq_sqrt]
      all_goals norm_num
      all_goals nlinarith
    have h2 : abs ((1 / 2 - Real.sqrt 3 / 2 * Complex.I : ℂ) ^ 2013) = 1 := by
      calc
        abs ((1 / 2 - Real.sqrt 3 / 2 * Complex.I : ℂ) ^ 2013)
          = abs ((1 / 2 - Real.sqrt 3 / 2 * Complex.I : ℂ) ) ^ 2013 := by
            simp [Complex.abs, Complex.normSq]
            <;> norm_num [abs_pow]
        _ = 1 ^ 2013 := by rw [h1]
        _ = 1 := by norm_num
    simpa using h2
  · -- Show that for any z1, z2 ∈ A, we have z1 * z2 ∈ A
    intro z1 z2 hz1 hz2
    constructor
    · -- Show that z1 * z2 ∈ A
      rw [hA] at *
      have h1 : abs z1 = 1 := by
        rw [hA] at hz1
        simpa using hz1
      have h2 : abs z2 = 1 := by
        rw [hA] at hz2
        simpa using hz2
      have h3 : abs (z1 * z2) = 1 := by
        calc
          abs (z1 * z2) = abs z1 * abs z2 := by
            simp [Complex.abs, Complex.normSq]
            <;> norm_num [abs_mul]
          _ = 1 * 1 := by rw [h1, h2]
          _ = 1 := by norm_num
      simpa using h3
    · -- Show existence of z1, z2, z3 ∈ A such that z1 + z2 + z3 = 3
      use (1 : ℂ), (1 : ℂ), (1 : ℂ)
      constructor
      · -- Show z1 ∈ A
        rw [hA]
        norm_num [Complex.abs, Complex.normSq]
        all_goals norm_num [Complex.I_sq]
      constructor
      · -- Show z2 ∈ A
        rw [hA]
        norm_num [Complex.abs, Complex.normSq]
        all_goals norm_num [Complex.I_sq]
      constructor
      · -- Show z3 ∈ A
        rw [hA]
        norm_num [Complex.abs, Complex.normSq]
        all_goals norm_num [Complex.I_sq]
      all_goals norm_num [Complex.ext_iff]