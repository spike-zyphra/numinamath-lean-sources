import Mathlib

open Polynomial

theorem number_theory_240617 : (¬∃ x : ℚ, Int.fract (x ^ 2) + Int.fract x = 1) ∧ ∃ x : ℝ, Int.fract (x ^ 2) + Int.fract x = 1 := by
  constructor
  .
    rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ : ∃ z : ℤ, x ^ 2 + x - z = 0 := by
      rcases Int.fract_add (x ^ 2) x with ⟨z, hz⟩
      use z + 1 + ⌊x ^ 2 + x⌋
      simp
      linarith [Int.floor_add_fract (x ^ 2 + x)]
    have hp₁ : (X ^ 2 + X - C z).natDegree = 2 := by compute_degree!
    have hp₂ : (X ^ 2 + X - C z).Monic := by
      rw [Monic.def, ← coeff_natDegree, hp₁]
      simp [-eq_intCast, coeff_X]
    have hp₃ : aeval x (X ^ 2 + X - C z) = 0 := by simp [hz]
    obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hp₂ hp₃
    obtain rfl : n = x := by simpa using hn
    rw [← Int.cast_pow, Int.fract_intCast, Int.fract_intCast] at hx
    simp at hx
  .
    use ((Real.sqrt 5 - 1) / 2)
    have h1 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
    have h2 : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
    have h3 : ((Real.sqrt 5 - 1 : ℝ) / 2) ^ 2 = (6 - 2 * Real.sqrt 5) / 4 := by
      nlinarith
    have h4 : ((Real.sqrt 5 - 1 : ℝ) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 := by
      rw [h3]
      ring_nf
    have h10 : Int.floor ((Real.sqrt 5 - 1 : ℝ) / 2) = 0 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try nlinarith [h1, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), h2])
    have h11 : Int.floor (((Real.sqrt 5 - 1 : ℝ) / 2) ^ 2) = 0 := by
      rw [h4]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try nlinarith [h1, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), h2])
    have h12 : Int.fract ((Real.sqrt 5 - 1 : ℝ) / 2) = ((Real.sqrt 5 - 1 : ℝ) / 2) := by
      rw [Int.fract]
      rw [h10]
      all_goals
        field_simp
    have h13 : Int.fract (((Real.sqrt 5 - 1 : ℝ) / 2) ^ 2) = ((Real.sqrt 5 - 1 : ℝ) / 2) ^ 2 := by
      rw [Int.fract]
      rw [h11]
      all_goals
        field_simp
    rw [h12, h13]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 1), sq_nonneg ((Real.sqrt 5 - 1 : ℝ) / 2)]