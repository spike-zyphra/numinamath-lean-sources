import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

theorem algebra_15207 :
  let m : ℝ := 4 + 2 * Real.sqrt 3
  ∀ (f g : ℝ → ℝ) (hf : f = fun x => x ^ 2 + 2) (hg : g = fun y => Real.sqrt (1 + m * y^2)),
  (∃ p : ℝ, f p = g p ∧
    (Nat.cast 2 : ℝ) * p = (fun y => m * y / Real.sqrt (1 + m * y^2)) p) := by
  intro m f g hf hg
  use Real.sqrt (Real.sqrt 3)
  have hm1 : m = 4 + 2 * Real.sqrt 3 := by rfl
  have hp1 : Real.sqrt (Real.sqrt 3) ^ 2 = Real.sqrt 3 := by
    rw [Real.sq_sqrt]
    positivity
  have h2 : f (Real.sqrt (Real.sqrt 3)) = g (Real.sqrt (Real.sqrt 3)) := by
    rw [hf, hg]
    have h3 : (Real.sqrt (Real.sqrt 3) : ℝ) ^ 2 = Real.sqrt 3 := by
      rw [Real.sq_sqrt]
      positivity
    simp [h3, hm1]
    have h4 : Real.sqrt (1 + (4 + 2 * Real.sqrt 3) * Real.sqrt 3) = 2 + Real.sqrt 3 := by
      have h5 : (1 + (4 + 2 * Real.sqrt 3) * Real.sqrt 3) = (2 + Real.sqrt 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h6 : Real.sqrt (1 + (4 + 2 * Real.sqrt 3) * Real.sqrt 3) = Real.sqrt ((2 + Real.sqrt 3) ^ 2) := by
        rw [h5]
      have h7 : Real.sqrt ((2 + Real.sqrt 3) ^ 2) = 2 + Real.sqrt 3 := by
        rw [Real.sqrt_sq (show 0 ≤ (2 + Real.sqrt 3 : ℝ) by positivity)]
      linarith [h6, h7]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ Real.sqrt 3 by positivity)]
  have h3 : (Nat.cast 2 : ℝ) * (Real.sqrt (Real.sqrt 3)) = (fun y => m * y / Real.sqrt (1 + m * y ^ 2)) (Real.sqrt (Real.sqrt 3)) := by
    have h3 : Real.sqrt (Real.sqrt 3) ^ 2 = Real.sqrt 3 := by
      rw [Real.sq_sqrt]
      positivity
    simp [h3, hm1]
    have h4 : Real.sqrt (1 + (4 + 2 * Real.sqrt 3) * Real.sqrt 3) = 2 + Real.sqrt 3 := by
      have h5 : (1 + (4 + 2 * Real.sqrt 3) * Real.sqrt 3) = (2 + Real.sqrt 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h6 : Real.sqrt (1 + (4 + 2 * Real.sqrt 3) * Real.sqrt 3) = Real.sqrt ((2 + Real.sqrt 3) ^ 2) := by
        rw [h5]
      have h7 : Real.sqrt ((2 + Real.sqrt 3) ^ 2) = 2 + Real.sqrt 3 := by
        rw [Real.sqrt_sq (show 0 ≤ (2 + Real.sqrt 3 : ℝ) by positivity)]
      linarith [h6, h7]
    rw [h4]
    field_simp [show (2 + Real.sqrt 3 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    ]
    <;> nlinarith [Real.sqrt_nonneg (Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ Real.sqrt 3 by positivity), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  constructor
  · exact h2
  · exact h3