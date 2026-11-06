import Mathlib

theorem algebra_257978 (A B C : ℝ) (h₀ : A < B) (h₁ : B < C)
    (h₂ : dist A B = dist B C) (h₃ : v₁ = 40) (h₄ : v₂ = 60) :
    (dist A C) / (dist A B / v₁ + dist B C / v₂) = 48 := by

  have h5 : dist A B = B - A := by
    simp [dist, abs_of_neg (show A - B < 0 by linarith)]

  have h6 : dist B C = C - B := by
    simp [dist, abs_of_neg (show B - C < 0 by linarith)]

  have h7 : dist A B = dist B C := h₂
  rw [h5] at h7
  rw [h6] at h7

  have h8 : dist A C = 2 * (dist A B) := by
    have h9 : dist A C = C - A := by
      simp [dist, abs_of_neg (show A - C < 0 by linarith)]
    have h10 : C = 2 * B - A := by
      linarith
    rw [h9]
    rw [h10]
    nlinarith [h5]

  have h11 : dist A B / v₁ + dist B C / v₂ = dist A B / 40 + dist B C / 60 := by
    rw [h₃, h₄]

  have h14 : dist B C = dist A B := by
    linarith

  rw [h11]

  rw [h14]

  have h16 : dist A B > 0 := by
    have h0 : dist A B = B - A := h5
    rw [h0]
    linarith

  rw [h8]

  field_simp [h16]
  nlinarith