import Mathlib

open Real Set
open scoped Real

theorem algebra_13078 (θ : Real) (hθ : θ ∈ Icc (π / 4) (π / 2)) (h : sin θ + cos θ = 4 * sqrt 2 / sqrt 17) :
    cos (2 * θ) = -8 / 17 := by
  have h1 : π / 4 ≤ θ := hθ.left
  have h2 : θ ≤ π / 2 := hθ.right
  have h3 : sin θ + cos θ = 4 * sqrt 2 / sqrt 17 := h
  have h4 : (sin θ + cos θ) ^ 2 = (4 * sqrt 2 / sqrt 17) ^ 2 := by
    rw [h3]
  have h5 : (sin θ + cos θ) ^ 2 = sin θ ^ 2 + cos θ ^ 2 + 2 * sin θ * cos θ := by ring
  have h6 : (4 * sqrt 2 / sqrt 17) ^ 2 = 32 / 17 := by
    calc
      (4 * sqrt 2 / sqrt 17) ^ 2
          = (4 * sqrt 2) ^ 2 / (sqrt 17 ^ 2) := by field_simp
      _ = (16 * (sqrt 2 ^ 2)) / (sqrt 17 ^ 2) := by ring
      _ = (16 * 2) / 17 := by simp [sq_sqrt]
      _ = 32 / 17 := by norm_num
  have h7 : sin θ ^ 2 + cos θ ^ 2 + 2 * sin θ * cos θ = 32 / 17 := by
    linarith [h4, h5, h6]
  have h8 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq θ
  have h9 : 2 * sin θ * cos θ = 15 / 17 := by
    linarith [h7, h8]
  have h10 : sin (2 * θ) = 15 / 17 := by
    rw [Real.sin_two_mul θ]
    linarith [h9]
  have h11 : cos (2 * θ) ^ 2 + sin (2 * θ) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (2 * θ)
  have h12 : cos (2 * θ) ^ 2 + (15 / 17) ^ 2 = 1 := by
    rw [←h10]
    exact h11
  have h13 : cos (2 * θ) ^ 2 = 64 / 289 := by
    linarith [h12]
  have h14 : cos (2 * θ) ≤ 0 := by
    have h14 : π / 2 ≤ 2 * θ := by
      linarith [h1]
    have h15 : 2 * θ ≤ π := by
      linarith [h2]
    have h16 : cos (2 * θ) ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      all_goals linarith
    exact h16
  have h15 : cos (2 * θ) = -8 / 17 := by
    nlinarith [h13, h14]
  exact h15