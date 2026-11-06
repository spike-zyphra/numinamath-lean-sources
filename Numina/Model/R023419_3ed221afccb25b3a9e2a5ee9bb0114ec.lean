import Mathlib

open Real Set
open scoped Real

theorem algebra_229817 (x : ℝ) (hx : x ∈ Icc (π/4) (π/2)) :
    sin x ^ 2 + sqrt 3 * sin x * cos x ∈ Icc 1 (3/2) := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x ^ 2 + sqrt 3 * sin x * cos x = 1 / 2 + sin (2 * x - π / 6) := by
    have h2 : sin x ^ 2 + sqrt 3 * sin x * cos x = 1 / 2 - (1 / 2) * cos (2 * x) + (sqrt 3 / 2) * sin (2 * x) := by
      have h3 : sin x ^ 2 = (1 - cos (2 * x)) / 2 := by
        rw [sin_sq_eq_half_sub]
        ring_nf
      have h4 : sin x * cos x = (1 / 2) * sin (2 * x) := by
        rw [sin_two_mul]
        <;> ring_nf
      rw [h3]
      have h5 : sqrt 3 * sin x * cos x = (sqrt 3 / 2) * sin (2 * x) := by
        calc
          sqrt 3 * sin x * cos x = sqrt 3 * (sin x * cos x) := by ring
          _ = sqrt 3 * ((1 / 2) * sin (2 * x)) := by rw [h4]
          _ = (sqrt 3 / 2) * sin (2 * x) := by ring
      linarith [h5]
    rw [h2]
    have h7 : (1 / 2 : ℝ) - (1 / 2 : ℝ) * cos (2 * x) + (sqrt 3 / 2) * sin (2 * x) = 1 / 2 + sin (2 * x - π / 6) := by
      have h8 : sin (2 * x - π / 6) = sin (2 * x) * cos (π / 6) - cos (2 * x) * sin (π / 6) := by
        rw [sin_sub]
      rw [h8]
      have h9 : cos (π / 6) = (sqrt 3 / 2 : ℝ) := by
        exact cos_pi_div_six
      have h10 : sin (π / 6) = (1 / 2 : ℝ) := by
        exact sin_pi_div_six
      rw [h9, h10]
      ring_nf
    linarith [h7]
  rw [h1]
  have h2x : π / 3 ≤ 2 * x - π / 6 ∧ 2 * x - π / 6 ≤ 5 * π / 6 := by 
    constructor
    · -- Show that π / 3 ≤ 2 * x - π / 6
      nlinarith [hx1, hx2, Real.pi_pos]
    · -- Show that 2 * x - π / 6 ≤ 5 * π / 6
      nlinarith [hx1, hx2, Real.pi_pos]
  have h3 : 1 / 2 ≤ sin (2 * x - π / 6) ∧ sin (2 * x - π / 6) ≤ 1 := by
    have h8 : sin (2 * x - π / 6) ≥ 1 / 2 := by 
      have ht1 : π / 3 ≤ 2 * x - π / 6 := by linarith [hx1, hx2, Real.pi_pos]
      have ht2 : 2 * x - π / 6 ≤ 5 * π / 6 := by linarith [hx1, hx2, Real.pi_pos]
      by_cases h9 : 2 * x - π / 6 ≤ π / 2
      · -- Case 1: π/3 ≤ t ≤ π/2
        have h10 : sin (2 * x - π / 6) ≥ sin (π / 6) := by 
          apply Real.sin_le_sin_of_le_of_le_pi_div_two
          all_goals nlinarith [ht1, h9, Real.pi_pos]
        have h11 : sin (π / 6) = 1 / 2 := by 
          exact sin_pi_div_six
        linarith [h10, h11]
      · -- Case 2: π/2 < t ≤ 5π/6
        have h9 : 2 * x - π / 6 > π / 2 := by linarith
        have ht3 : 2 * x - π / 6 ≤ 5 * π / 6 := by linarith [hx1, hx2, Real.pi_pos]
        have h11 : sin (2 * x - π / 6) = sin (π - (2 * x - π / 6)) := by 
          rw [show π - (2 * x - π / 6) = π - (2 * x - π / 6) by ring]
          rw [sin_pi_sub]
        have ht4 : π - (2 * x - π / 6) ≥ π / 6 := by
          nlinarith [h9, ht3, Real.pi_pos]
        have ht5 : π - (2 * x - π / 6) ≤ π / 2 := by 
          nlinarith [h9, ht3, Real.pi_pos]
        have h13 : sin (π - (2 * x - π / 6)) ≥ sin (π / 6) := by 
          apply Real.sin_le_sin_of_le_of_le_pi_div_two
          all_goals nlinarith [ht4, ht5, Real.pi_pos]
        have h12 : sin (π / 6) = 1 / 2 := by 
          exact sin_pi_div_six
        have h14 : sin (2 * x - π / 6) ≥ 1 / 2 := by 
          linarith [h11, h13, h12]
        linarith [h14]
    have h9 : sin (2 * x - π / 6) ≤ 1 := by 
      apply sin_le_one 
    constructor 
    · linarith [h8] 
    · linarith [h9]
  constructor 
  · -- Show that 1 ≤ 1 / 2 + sin (2 * x - π / 6)
    linarith [h3.1] 
  · -- Show that 1 / 2 + sin (2 * x - π / 6) ≤ 3 / 2 
    linarith [h3.2]