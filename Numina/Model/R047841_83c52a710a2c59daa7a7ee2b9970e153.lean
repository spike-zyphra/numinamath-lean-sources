import Mathlib

open BigOperators Real Set

theorem algebra_9288 (a b : ℝ) (ha : a > 0) (f : ℝ → ℝ)
    (hf : f = fun x => x ^ 3 - 3 * a * x + b)
    (x₁ : ℝ) (hx₁ : f x₁ = 6) (hmax : IsLocalMax f x₁) (x₂ : ℝ) (hx₂ : f x₂ = 2) (hmin : IsLocalMin f x₂) : AntitoneOn f (Icc (-1) 1) ∧ MonotoneOn f (Iic (-1)) ∧ MonotoneOn f (Ici 1) := by

  have h1 : ∀ x, (deriv f x) = 3 * x ^ 2 - 3 * a := by
    intro x
    rw [hf]
    simp [deriv_pow, deriv_const, mul_comm]
    all_goals field_simp
    <;> ring

  have h3 : deriv f x₁ = 0 := by
    apply hmax.deriv_eq_zero

  have h4 : deriv f x₂ = 0 := by
    apply hmin.deriv_eq_zero

  rw [h1] at h3 h4

  have h5 : x₁ ^ 2 = a := by
    nlinarith

  have h6 : x₂ ^ 2 = a := by
    nlinarith

  have h7 : f x₁ = x₁ ^ 3 - 3 * a * x₁ + b := by
    rw [hf]

  have h8 : f x₂ = x₂ ^ 3 - 3 * a * x₂ + b := by
    rw [hf]

  rw [h7] at hx₁
  rw [h8] at hx₂

  have h14 : x₂ = -x₁ := by
    have h12 : (x₁ + x₂) * (x₁ - x₂) = 0 := by
      nlinarith [h5, h6]
    cases (mul_eq_zero.mp h12) with
    | inl h13 =>
      have h14 : x₁ = -x₂ := by linarith
      nlinarith [sq_nonneg (x₁ ^ 2 - 1), sq_nonneg (x₂ ^ 2 - 1), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂)]
    | inr h13 =>
      have h14 : x₁ = x₂ := by linarith
      nlinarith [sq_nonneg (x₁ ^ 2 - 1), sq_nonneg (x₂ ^ 2 - 1), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂)]
  rw [show x₂ = -x₁ by linarith [h14]] at hx₂

  have h10 : b = 4 := by
    nlinarith [sq_nonneg (x₁ ^ 2 - 1), sq_nonneg (x₁ ^ 2 - 1), sq_nonneg (x₁ + 1), sq_nonneg (x₁ - 1)]

  have h11 : a = 1 := by
    nlinarith [sq_nonneg (x₁ ^ 2 - 1), sq_nonneg (x₁ ^ 2 - 1), sq_nonneg (x₁ + 1), sq_nonneg (x₁ - 1)]

  have h13 : f = fun x => x ^ 3 - 3 * (1 : ℝ) * x + (4 : ℝ) := by
    rw [hf]
    simp [h11, h10]

  constructor
  · -- Proof that f is antitone on Icc (-1) 1
    intro x hx y hy hxy
    rw [h13]
    simp at hx hy ⊢
    have h15 : -1 ≤ x := hx.1
    have h16 : x ≤ 1 := hx.2
    have h17 : -1 ≤ y := hy.1
    have h18 : y ≤ 1 := hy.2
    have h19 : x ≤ y := hxy
    have h20 : x ^ 3 - 3 * (1 : ℝ) * x + (4 : ℝ) ≥ y ^ 3 - 3 * (1 : ℝ) * y + (4 : ℝ) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - 1), sq_nonneg (y - 1),
        mul_nonneg (show (0 : ℝ) ≤ 1 + x by nlinarith) (show (0 : ℝ) ≤ 1 - x by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ 1 + y by nlinarith) (show (0 : ℝ) ≤ 1 - y by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ y - x by nlinarith) (show (0 : ℝ) ≤ 1 - x by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ y - x by nlinarith) (show (0 : ℝ) ≤ 1 - y by nlinarith)]
    linarith
  constructor
  · -- Proof that f is monotone on Iic (-1)
    intro x hx y hy hxy
    rw [h13]
    simp at hx hy ⊢
    have h15 : x ≤ -1 := by linarith
    have h16 : y ≤ -1 := by linarith
    have h17 : x ≤ y := hxy
    have h20 : x ^ 3 - 3 * (1 : ℝ) * x + (4 : ℝ) ≤ y ^ 3 - 3 * (1 : ℝ) * y + (4 : ℝ) := by
      nlinarith [sq_nonneg (y - x), sq_nonneg (y + 1), sq_nonneg (x + 1), mul_nonneg (show (0 : ℝ) ≤ -x - 1 by nlinarith) (show (0 : ℝ) ≤ -y - 1 by nlinarith)]
    linarith
  · -- Proof that f is monotone on Ici 1
    intro x hx y hy hxy
    rw [h13]
    simp at hx hy ⊢
    have h15 : 1 ≤ x := by linarith
    have h16 : 1 ≤ y := by linarith
    have h17 : x ≤ y := hxy
    have h20 : x ^ 3 - 3 * (1 : ℝ) * x + (4 : ℝ) ≤ y ^ 3 - 3 * (1 : ℝ) * y + (4 : ℝ) := by
      nlinarith [sq_nonneg (y - x), sq_nonneg (y - 1), sq_nonneg (x - 1), mul_nonneg (show (0 : ℝ) ≤ x - 1 by nlinarith) (show (0 : ℝ) ≤ y - 1 by nlinarith)]
    linarith