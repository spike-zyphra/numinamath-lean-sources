import Mathlib

theorem algebra_1149 {m n a : ℝ} (hmn : m ≠ n) (h₁ : m^2 - 2 * m = a) (h₂ : n^2 - 2 * n = a)
    (h₃ : m^2 + n^2 = 5) : a = 1 / 2 := by 
  have h₄ : m^2 - n^2 - 2 * (m - n) = 0 := by
    have eq_sub : m^2 - 2 * m - (n^2 - 2 * n) = 0 := by linarith [h₁, h₂]
    have : m^2 - n^2 - 2 * (m - n) = (m^2 - 2 * m) - (n^2 - 2 * n) := by
      ring
    rw [this] at *
    linarith [eq_sub]

  have h₅ : (m - n) * (m + n - 2) = 0 := by
    ring_nf at h₄ ⊢
    linarith
  
  cases (mul_eq_zero.mp h₅) with
  | inl h₆ =>
    exfalso
    apply hmn
    linarith
  | inr h₇ =>
    have h₈ : m + n = 2 := by linarith
    have h₉ : m^2 + n^2 - 2 * (m + n) = 2 * a := by
      nlinarith [h₁, h₂]
    rw [h₃, h₈] at h₉
    nlinarith