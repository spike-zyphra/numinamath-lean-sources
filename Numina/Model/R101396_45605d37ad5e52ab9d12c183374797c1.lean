import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_142033 (a : ℝ) (f : ℝ → ℝ)
  (hf : f = λ x => sqrt 3 * sin (2 * x) + 2 * (cos x)^2 + a)
  (hmin : IsLeast {y | ∃ x ∈ Icc 0 (π / 2), f x = y} (-1)) :
  a = -1 := by
  rcases hmin with ⟨h1, h2⟩
  rcases h1 with ⟨x, hx, hx2⟩
  have h3 : 0 ≤ x := hx.1
  have h4 : x ≤ π / 2 := hx.2
  have h5 : f x = sqrt 3 * sin (2 * x) + 2 * (cos x)^2 + a := by
    rw [hf]
  rw [h5] at hx2
  have h6 : ∃ y, y ∈ Icc (0 : ℝ) (π / 2) ∧ f y = a := by
    use π / 2
    constructor
    · -- Show π / 2 ∈ [0, π / 2]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show f (π / 2) = a
      rw [hf]
      simp [show 2 * (π / 2) = π by ring, sin_pi, cos_pi_div_two]
      all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  rcases h6 with ⟨y, hy, hy2⟩
  have h7 : -1 ≤ a := by
    apply h2
    · exact ⟨y, hy, hy2⟩
  have h8 : ∀ x ∈ Icc (0 : ℝ) (π / 2), f x ≥ a := by
    intro x hx
    have h9 : f x = sqrt 3 * sin (2 * x) + 2 * (cos x)^2 + a := by
      rw [hf]
    rw [h9]
    have h10 : sqrt 3 * sin (2 * x) + 2 * (cos x)^2 ≥ 0 := by
      have h11 : 0 ≤ x := hx.1
      have h12 : x ≤ π / 2 := hx.2
      have h13 : 0 ≤ sqrt 3 := Real.sqrt_nonneg 3
      have h14 : sin (2 * x) ≥ 0 := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
      have h15 : (cos x)^2 ≥ 0 := by positivity
      nlinarith [sq_nonneg (sin (2 * x)), sq_nonneg (cos x), sq_nonneg (sqrt 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq x, Real.sin_two_mul x, mul_self_nonneg (sin x - cos x), mul_self_nonneg (sin x + cos x), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
    linarith
  have h9 : f x ≥ a := h8 x ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  linarith [hx2, h9, h7]