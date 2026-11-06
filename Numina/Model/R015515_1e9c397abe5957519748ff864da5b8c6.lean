import Mathlib

theorem algebra_270462 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h : ∀ n, a n * (a n - a (n - 1)) = 1 / Real.sqrt n * (1 / Real.sqrt n + a (n - 1)))
    (ha1 : a 1 = 1) :
    (∀ n, a n = 1 / Real.sqrt n) ∧
    (∀ b : Finset ℕ, b.card > 0 → ∀ i ∈ b, 0 < i →
      a b.card ≤ ∑ i ∈ b, Real.sqrt i / (i + 1)) := by

  have h1 := h 1
  have h2 : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one

  simp [show Real.sqrt (1 : ℝ) = (1 : ℝ) by exact Real.sqrt_one] at h1
  rw [ha1] at h1

  have ha0 : 0 < a 0 := ha 0

  have h3 : a 0 = 0 := by
    nlinarith

  linarith [h3, ha0]