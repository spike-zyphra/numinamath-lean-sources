import Mathlib

open Real

/-- `f k x y` denotes that $4*x^2 - 6*k*x*y + (3*k^2+2)*y^2 - 4*x - 4*y + 6
$-/
def f_4098 (k : ℝ) x y := 4*x^2 - 6*k*x*y + (3*k^2+2)*y^2 - 4*x - 4*y + 6

lemma p86' : ∀ (x y k : ℝ),
          f_4098 k x y = (x-2)^2 + 2*(y-1)^2 + 3*(x-k*y)^2 := by
  intro x y k
  dsimp [f_4098]
  nlinarith

theorem intermediate_algebra_4098 {k : ℝ} : k = 2 ↔
      (∀ (x y : ℝ), 0 ≤ f_4098 k x y) ∧ ∃ x, ∃ y, f_4098 k x y = 0 := by
  constructor
  · -- Show that k=2 implies the quadratic form is non-negative and equals zero
    intro hk
    constructor
    · -- Show that for any x, y, the quadratic form is non-negative
      intro x y
      rw [p86' x y k]
      rw [hk]
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x - 2 * y)]
    · -- Show there exists a point where the quadratic form equals zero
      use 2, 1
      rw [p86' 2 1 k]
      rw [hk]
      norm_num
  · -- Show that if the quadratic form is non-negative and equals zero, then k=2
    rintro ⟨h₁, h₂⟩
    rcases h₂ with ⟨x₁, y₁, h₂⟩
    have eq₁ : f_4098 k x₁ y₁ = (x₁ - 2) ^ 2 + 2 * (y₁ - 1) ^ 2 + 3 * (x₁ - k * y₁) ^ 2 := (p86' x₁ y₁ k)
    rw [eq₁] at h₂
    have term₁ : (x₁ - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x₁ - 2), sq_nonneg (y₁ - 1), sq_nonneg (x₁ - k * y₁)]
    have term₂ : (y₁ - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x₁ - 2), sq_nonneg (y₁ - 1), sq_nonneg (x₁ - k * y₁)]
    have term₃ : (x₁ - k * y₁) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x₁ - 2), sq_nonneg (y₁ - 1), sq_nonneg (x₁ - k * y₁)]
    have hx₁ : x₁ = 2 := by
      nlinarith
    have hy₁ : y₁ = 1 := by
      nlinarith
    have h_eq : x₁ = k * y₁ := by
      nlinarith
    rw [hx₁, hy₁] at h_eq
    nlinarith