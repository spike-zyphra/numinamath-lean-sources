import Mathlib

theorem algebra_310464 {a b c d : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = a * x ^ 4 + b * (Real.sin x) ^ 3 + c * x ^ 2 + d * x + 2)
    (h₁ : f 1 = 7) (h₂ : f (-1) = 9) (h₃ : f 2 + f (-2) = 124) :
    f (Real.sqrt 2) + f (-Real.sqrt 2) = 40 := by

  have eq1 : f 1 + f (-1) = 2 * a + 2 * c + 4 := by
    rw [h₀ 1, h₀ (-1)]
    have h1 : Real.sin (-1:ℝ) = -Real.sin 1 := by
      rw [show (-1:ℝ) = - (1:ℝ) by ring]
      rw [Real.sin_neg]
    simp only [h1]
    ring_nf

  have h_eq1 : 2 * a + 2 * c + 4 = 16 := by
    have h11 : f 1 + f (-1) = 16 := by linarith [h₁, h₂]
    linarith [h11, eq1]

  have eq2 : a + c = 6 := by
    linarith [h_eq1]

  have eq3 : f 2 + f (-2) = 32 * a + 8 * c + 4 := by
    rw [h₀ 2, h₀ (-2)]
    have h1 : Real.sin (-2:ℝ) = -Real.sin 2 := by
      rw [show (-2:ℝ) = - (2:ℝ) by ring]
      rw [Real.sin_neg]
    simp only [h1]
    ring_nf

  have eq4 : 4 * a + c = 15 := by 
    nlinarith [h₃, eq3]

  have ha : a = 3 := by 
    linarith [eq2, eq4]

  have hc : c = 3 := by 
    linarith [eq2, ha]

  have eq5 : f (Real.sqrt 2) + f (-Real.sqrt 2) = 2 * a * (Real.sqrt 2) ^ 4 + 2 * c * (Real.sqrt 2) ^ 2 + 4 := by
    rw [h₀ (Real.sqrt 2), h₀ (-Real.sqrt 2)]
    have h1 : Real.sin (-Real.sqrt 2) = -Real.sin (Real.sqrt 2) := by 
      rw [show (-Real.sqrt 2 : ℝ) = - (Real.sqrt 2 : ℝ) by ring]
      rw [Real.sin_neg]
    simp only [h1]
    ring_nf

  have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 : (Real.sqrt 2 : ℝ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 4 = ((Real.sqrt 2 : ℝ) ^ 2) ^ 2 := by ring
      _ = (2) ^ 2 := by rw [h1]
      _ = (4 : ℝ) := by norm_num

  rw [eq5]
  rw [h1, h2, ha, hc]
  norm_num