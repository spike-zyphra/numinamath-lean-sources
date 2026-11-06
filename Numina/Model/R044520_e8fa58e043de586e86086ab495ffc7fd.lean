import Mathlib

open Real

theorem inequalities_109984 (c : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → x^2 + y^2 = 1 → x^6 + y^6 ≥ c * x * y) ↔
    c ≤ 1 / 2 := by
  constructor
  · -- Assume the inequality holds for all $x, y > 0$ with $x^2 + y^2 = 1$.
    intro h
    have h1 := h (Real.sqrt (1 / 2)) (Real.sqrt (1 / 2)) (by positivity) (by positivity) (by
        have h1 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
        nlinarith)
    have h2 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt (1 / 2) : ℝ) ^ 6 = (1 / 8 : ℝ) := by
      calc
        (Real.sqrt (1 / 2) : ℝ) ^ 6 = ((Real.sqrt (1 / 2) ^ 2) ^ 3) := by ring
        _ = ( (1 / 2) ^ 3 ) := by rw [h2]
        _ = (1 / 8 : ℝ) := by norm_num
    have h4 : (Real.sqrt (1 / 2) : ℝ) ^ 6 + (Real.sqrt (1 / 2) : ℝ) ^ 6 = (1 / 4 : ℝ) := by
      rw [h3]
      norm_num
    have h5 : (Real.sqrt (1 / 2) : ℝ) * (Real.sqrt (1 / 2) : ℝ) = (1 / 2 : ℝ) := by
      nlinarith [h2]
    nlinarith [h4, h5, h1]
  · -- Assume $c \leq \frac{1}{2}$, prove the inequality for all $x, y > 0$ with $x^2 + y^2 = 1$.
    intro hc x y hx hy h
    have h1 : x ^ 6 + y ^ 6 ≥ (1 / 2) * (x * y) := by
      have h2 : x ^ 2 + y ^ 2 = 1 := h
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - 1 / 2), sq_nonneg (y ^ 2 - 1 / 2), 
        sq_nonneg (x * y - 1 / 2), 
        sq_nonneg (x ^ 2 + y ^ 2 - 1), 
        mul_pos hx hy,
        sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), 
        sq_nonneg (x ^ 2 + y ^ 2 - 1)]
    nlinarith [h1, hc, mul_pos hx hy]