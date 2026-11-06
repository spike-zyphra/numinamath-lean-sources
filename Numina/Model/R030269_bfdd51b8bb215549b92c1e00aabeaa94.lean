import Mathlib 

namespace calculus_610984 

theorem Cauchy_Schwarz_Ineq (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h : 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2
  calc
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by ring
    _ ≥ 0 := pow_two_nonneg (a * d - b * c)
  calc
    (a * c + b * d) ^ 2  = (a * c + b * d) ^ 2 + 0 := by rw [add_zero]
    _ ≤ (a * c + b * d) ^ 2 + ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2) :=
    (add_le_add_iff_left _).2 h
    _ = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring

end calculus_610984 
open Real calculus_610984 

theorem calculus_610984 : IsLeast {a | ∃ x : ℝ, |2 + sin x - cos x| = a} (2 - √2) := by
  constructor
  · -- Show that 2 - √2 is in the set.
    use -Real.pi / 4
    have h1 : sin (-Real.pi / 4) = -Real.sqrt 2 / 2 := by
      have h2 : sin (-Real.pi / 4) = - sin (Real.pi / 4) := by
        rw [show -Real.pi / 4 = - (Real.pi / 4) by ring]
        simp [sin_neg]
      rw [h2]
      rw [sin_pi_div_four]
      all_goals ring
    have h2 : cos (-Real.pi / 4) = Real.sqrt 2 / 2 := by
      have h3 : cos (-Real.pi / 4) = cos (Real.pi / 4) := by
        rw [show -Real.pi / 4 = - (Real.pi / 4) by ring]
        simp [cos_neg]
      rw [h3]
      rw [cos_pi_div_four]
    have h3 : (2 + sin (-Real.pi / 4) - cos (-Real.pi / 4) : ℝ) = (2 - Real.sqrt 2 : ℝ) := by
      rw [h1, h2]
      ring
    have h4 : (2 - Real.sqrt 2 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h3]
    rw [abs_of_nonneg h4]
    all_goals linarith
  · -- Show that 2 - √2 is the least element in the set.
    intro a ha
    rcases ha with ⟨x, hx⟩
    have h1 : |2 + sin x - cos x| = a := by
      linarith [hx]
    have h4 : (sin x - cos x) ≥ -Real.sqrt 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg (sin x + Real.sqrt 2 / 2), sq_nonneg (cos x - Real.sqrt 2 / 2), 
            Real.sin_sq_add_cos_sq x, 
              sq_nonneg (sin x - cos x + Real.sqrt 2), sq_nonneg (sin x - cos x - Real.sqrt 2)]
    have h5 : (sin x - cos x) ≤ Real.sqrt 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg (sin x - Real.sqrt 2 / 2), sq_nonneg (cos x + Real.sqrt 2 / 2), 
            Real.sin_sq_add_cos_sq x, 
              sq_nonneg (sin x - cos x - Real.sqrt 2), sq_nonneg (sin x - cos x + Real.sqrt 2)]
    have h6 : (2 + sin x - cos x : ℝ) ≥ (2 - Real.sqrt 2 : ℝ) := by
      nlinarith [h4]
    cases abs_cases (2 + sin x - cos x) with
    | inl h =>
      nlinarith [h6, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    | inr h =>
      nlinarith [h6, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]