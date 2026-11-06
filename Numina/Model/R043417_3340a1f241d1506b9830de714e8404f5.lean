import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_252889 {f : ℝ → ℝ}
  (hf : f = λ x => ((x + 1)^2 + log (sqrt (x^2 + 1) + x)) / (x^2 + 1))
  (M N : ℝ)
  (hM : ∃ x, f x = M)
  (hN : ∃ x, f x = N)
  (hMub : ∀ x, f x ≤ M)
  (hNlb : ∀ x, f x ≥ N) :
  M + N = 2 := by
  have h1 : ∀ x : ℝ, f x + f (-x) = 2 := by
    intro x
    rw [hf]
    simp 
    have h2 : log (Real.sqrt (x ^ 2 + 1) + x) + log (Real.sqrt ((-x) ^ 2 + 1) + (-x)) = 0 := by 
      have h3 : Real.sqrt ((-x) ^ 2 + 1) = Real.sqrt (x ^ 2 + 1) := by
        have h4 : (-x) ^ 2 + 1 = x ^ 2 + 1 := by
          ring_nf
        rw [h4]
      rw [h3]
      have h4 : (Real.sqrt (x ^ 2 + 1) + x) * (Real.sqrt (x ^ 2 + 1) + (-x)) = 1 := by
        have h5 : (Real.sqrt (x ^ 2 + 1) + x) * (Real.sqrt (x ^ 2 + 1) + (-x)) =
            (Real.sqrt (x ^ 2 + 1)) ^ 2 - x ^ 2 := by 
          ring_nf
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith)]
      have h6 : Real.sqrt (x ^ 2 + 1) + x > 0 := by
        have h7 : Real.sqrt (x ^ 2 + 1) > 0 := by positivity
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith)]
      have h8 : Real.sqrt (x ^ 2 + 1) + (-x) > 0 := by 
        have h9 : Real.sqrt (x ^ 2 + 1) ≥ |x| := by
          cases' abs_cases x with hx hx
          · nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith)]
          · nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith)]
        cases' abs_cases x with hx hx
        · nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]
        · nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]
      have h7 : log (Real.sqrt (x ^ 2 + 1) + x) + log (Real.sqrt (x ^ 2 + 1) + (-x)) =
          log ((Real.sqrt (x ^ 2 + 1) + x) * (Real.sqrt (x ^ 2 + 1) + (-x))) := by 
        rw [← Real.log_mul (by positivity) (by positivity)]
      rw [h7]
      rw [h4]
      simp
    have h3 : (x + 1) ^ 2 + (1 - x) ^ 2 = 2 * (x ^ 2 + 1) := by
      nlinarith
    field_simp [(show x^2 + 1 ≠ 0 by nlinarith)] at *
    nlinarith [h2, h3]
  have h2 : ∃ x, f x = M := hM
  rcases h2 with ⟨x, hx⟩
  have h3 : ∃ x, f x = N := hN
  rcases h3 with ⟨y, hy⟩
  have h4 : f x + f (-x) = 2 := h1 x
  have h5 : f (-x) ≥ N := by
    apply hNlb
  have h6 : f y + f (-y) = 2 := h1 y
  have h7 : f (-y) ≤ M := by
    apply hMub
  nlinarith [hx, h4, h5, hy, h6, h7]