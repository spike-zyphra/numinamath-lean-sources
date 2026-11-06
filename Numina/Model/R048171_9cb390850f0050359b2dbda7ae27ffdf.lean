import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-- Let $f_n (x) = \text{sin}^n x + \text{cos}^n x.$ -/
noncomputable def f (n : ℕ) (x : ℝ) := (sin x)^n + (cos x)^n

theorem algebra_1130 : ∀ x, 6 * (f 4 x) - 4 *(f 6 x) = 2 * (f 2 x) := by
  intro x
  simp [f]
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h2 : sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x * cos x) ^ 2 := by
    ring
  have h3 : sin x ^ 6 + cos x ^ 6 = (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 + cos x ^ 2) * (sin x * cos x) ^ 2 := by
    ring
  have eq1 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 := by
    rw [h2, h1]
    <;> nlinarith
  have eq2 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * (sin x * cos x) ^ 2 := by
    rw [h3, h1]
    <;> nlinarith
  have h4 : 6 * (sin x ^ 4 + cos x ^ 4) - 4 * (sin x ^ 6 + cos x ^ 6) = 2 := by
    rw [eq1, eq2]
    nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x * cos x), sq_nonneg (sin x), sq_nonneg (cos x), sq_nonneg (sin x - cos x)]
  have h5 : 2 * (sin x ^ 2 + cos x ^ 2) = 2 := by
    have h1' : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact h1
    nlinarith
  linarith [h4, h5]