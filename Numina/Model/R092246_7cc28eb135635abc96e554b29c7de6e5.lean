import Mathlib

open Real Set

theorem algebra_296405 {f : ℝ → ℝ} (hf : f = fun x => sqrt (x^2) + 4 + sqrt ((8 - x)^2) + 16) :
    IsLeast (range f) (f (8 / 3)) := by
  have h1 : f (8 / 3) = 28 := by
    rw [hf]
    have h2 : sqrt ((8 / 3 : ℝ) ^ 2) = (8 / 3 : ℝ) := by
      rw [Real.sqrt_sq (by norm_num)]
    have h3 : sqrt ((8 - (8 / 3 : ℝ)) ^ 2) = (16 / 3 : ℝ) := by
      have h4 : (8 - (8 / 3 : ℝ)) ^ 2 = (16 / 3 : ℝ) ^ 2 := by norm_num
      rw [h4]
      rw [Real.sqrt_sq (by norm_num)]
    simp [h2, h3]
    all_goals norm_num
  constructor
  · -- Show that f(8/3) is in the range of f
    simpa using by norm_num
  · -- Show that f(8/3) ≤ y for all y ∈ range f
    intro y
    rintro ⟨x, hx⟩
    have hfx : y = f x := by
      linarith [hx]
    rw [hfx]
    rw [h1]
    have hfx_def : f x = sqrt (x ^ 2) + 4 + sqrt ((8 - x : ℝ) ^ 2) + 16 := by
      rw [hf]
    have h3 : sqrt (x ^ 2) = |x| := by
      rw [Real.sqrt_sq_eq_abs]
    have h4 : sqrt ((8 - x : ℝ) ^ 2) = |8 - x| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [hfx_def, h3, h4]
    have h5 : |x| + |8 - x| ≥ 8 := by
      cases abs_cases x with
      | inl h1 =>
        cases abs_cases (8 - x) with
        | inl h2 =>
          nlinarith
        | inr h2 =>
          nlinarith
      | inr h1 =>
        cases abs_cases (8 - x) with
        | inl h2 =>
          nlinarith
        | inr h2 =>
          nlinarith
    linarith