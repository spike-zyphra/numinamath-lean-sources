import Mathlib

theorem calculus_33969 (a b c : ℝ) (h : ∀ x, |x| ≤ 1 → |a * x ^ 2 + b * x + c| ≤ 1)
    (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c) :
    ∀ x, |x| ≤ 1 → |deriv f x| ≤ 4 := by 
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h 0 (by norm_num)
  have h10 : deriv f x = 2 * a * x + b := by
    rw [funext hf]
    simp [deriv_pow, deriv_add, deriv_mul, mul_comm b, mul_assoc a]
    all_goals field_simp
    <;> ring_nf <;> simp [mul_comm b, mul_assoc a] <;> ring
  rw [h10]
  have h11 : -1 ≤ x := by linarith [abs_le.mp hx]
  have h12 : x ≤ 1 := by linarith [abs_le.mp hx]
  have h13 : -4 ≤ 2 * a * x + b := by 
    cases' abs_le.mp h1 with h1u h1l
    cases' abs_le.mp h2 with h2u h2l
    cases' abs_le.mp h3 with h3u h3l
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (a * (x^2)), sq_nonneg (b - a * 2 * x), sq_nonneg (c - 1), sq_nonneg (c + 1)]
  have h14 : 2 * a * x + b ≤ 4 := by 
    cases' abs_le.mp h1 with h1u h1l
    cases' abs_le.mp h2 with h2u h2l
    cases' abs_le.mp h3 with h3u h3l
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (a * (x^2)), sq_nonneg (b - a * 2 * x), sq_nonneg (c - 1), sq_nonneg (c + 1)]
  apply abs_le.mpr 
  constructor
  · nlinarith
  · nlinarith