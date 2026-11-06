import Mathlib

theorem algebra_21613 (f g : ℝ → ℝ)
    (hf : f = fun x => x ^ 2) (hg : g = fun x => 1 - x) :
    ∃ x1 x2, x1 ≠ x2 ∧ f x1 = g x1 ∧ f x2 = g x2 ∧
    Real.sqrt ((x2 - x1) ^ 2 + (g x2 - g x1) ^ 2) = Real.sqrt 10 := by

  use (-1 + Real.sqrt 5) / 2, (-1 - Real.sqrt 5) / 2

  constructor
  · -- Show that x1 ≠ x2
    by_contra h
    have h1 : Real.sqrt 5 = 0 := by
      nlinarith
    have h2 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  constructor
  · -- Show that f(x1) = g(x1)
    rw [hf, hg]
    have h1 : ((-1 + Real.sqrt 5) / (2 : ℝ)) ^ 2 = 1 - ((-1 + Real.sqrt 5) / (2 : ℝ)) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    simp_all [h1]
  constructor
  · -- Show that f(x2) = g(x2)
    rw [hf, hg]
    have h2 : ((-1 - Real.sqrt 5) / (2 : ℝ)) ^ 2 = 1 - ((-1 - Real.sqrt 5) / (2 : ℝ)) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    simp_all [h2]
  · -- Show that the distance is sqrt(10)
    have h3 : ((-1 - Real.sqrt 5) / (2 : ℝ) - (-1 + Real.sqrt 5) / (2 : ℝ) ) ^ 2 = 5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    have h4 : (g ((-1 - Real.sqrt 5) / 2) - g ((-1 + Real.sqrt 5) / 2) ) ^ 2 = 5 := by
      rw [hg]
      have h5 : (1 - ((-1 - Real.sqrt 5 : ℝ) / 2) ) - (1 - ((-1 + Real.sqrt 5 : ℝ) / 2) ) = Real.sqrt 5 := by
        linarith
      simp [h5]
      <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    have h6 : ((-1 - Real.sqrt 5) / (2 : ℝ) - (-1 + Real.sqrt 5) / (2 : ℝ) ) ^ 2 + (g ((-1 - Real.sqrt 5) / 2) - g ((-1 + Real.sqrt 5) / 2) ) ^ 2 = 10 := by
      rw [h3, h4]
      <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    rw [h6]
    <;> norm_num