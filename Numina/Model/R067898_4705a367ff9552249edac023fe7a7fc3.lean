import Mathlib

theorem algebra_278602 {p : ℝ} (x₁ x₂ : ℝ) (hx₁ : x₁^2 + p * x₁ + 4 = 0) (hx₂ : x₂^2 + p * x₂ + 4 = 0)
    (hne : x₁ ≠ x₂) :
    |x₁ + x₂| > 4 := by
  have h1 : x₁ - x₂ ≠ 0 := sub_ne_zero_of_ne hne
  have h2 : x₁^2 - x₂^2 + p * (x₁ - x₂) = 0 := by
    linarith
  have h3 : (x₁ - x₂) * (x₁ + x₂ + p) = 0 := by
    ring_nf at h2 ⊢
    linarith
  have h4 : x₁ + x₂ + p = 0 := by
    apply_fun (fun y => y / (x₁ - x₂)) at h3
    field_simp [h1] at h3
    linarith
  have h5 : (x₁ - x₂) ^ 2 > 0 := by
    exact sq_pos_of_ne_zero h1
  have h6 : x₁ + x₂ = -p := by
    linarith
  have h7 : x₁ * x₂ = 4 := by
    -- Add both equations x₁^2 + p * x₁ + 4 = 0 and x₂^2 + p * x₂ + 4 = 0
    have h8 : x₁^2 + x₂^2 + p * (x₁ + x₂) + 8 = 0 := by
      nlinarith [hx₁, hx₂]
    rw [show x₁ + x₂ = -p by linarith [h6]] at h8
    nlinarith [h6]
  have h8 : p ^ 2 > 16 := by
    have h9 : (x₁ - x₂) ^ 2 > 0 := h5
    have h10 : (x₁ - x₂) ^ 2 = (x₁ + x₂) ^ 2 - 4 * (x₁ * x₂) := by
      nlinarith
    rw [h10] at h9
    rw [h6, h7] at h9
    nlinarith
  have h9 : |x₁ + x₂| = |p| := by
    rw [show x₁ + x₂ = -p by linarith [h6]]
    rw [abs_neg]
  rw [h9]
  by_cases hp : p ≥ 0
  · -- If p >= 0, then |p| = p
    rw [abs_of_nonneg hp]
    nlinarith
  · -- If p < 0, then |p| = -p
    rw [abs_of_neg (show p < 0 by nlinarith)]
    nlinarith