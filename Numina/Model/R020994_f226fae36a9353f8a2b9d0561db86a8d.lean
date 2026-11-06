import Mathlib

theorem number_theory_117538 (x y : ℤ) (hx : x > 0) (hy : y > 0) :
    x ^ 3 - y ^ 3 = x * y + 61 ↔ (x, y) = (6, 5) := by
  constructor
  · -- Assume x^3 - y^3 = x * y + 61, prove (x, y) = (6, 5)
    intro h
    have h_eq : x ^ 3 - y ^ 3 = x * y + 61 := h
    -- Rearranging to x^3 - y^3 = x*y + 61
    have h1 : x  > y := by
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x - 6 : ℤ), sq_nonneg (y - 5 : ℤ)]
    have h2 : x ≤ 10 := by
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x - 6 : ℤ), sq_nonneg (y - 5 : ℤ)]
    have h3 : y ≤ 10 := by
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x - 6 : ℤ), sq_nonneg (y - 5 : ℤ)]
    interval_cases x <;> interval_cases y
    <;> norm_num at h_eq ⊢
    <;> tauto
  · -- Assume (x, y) = (6, 5), prove x^3 - y^3 = x * y + 61
    rintro ⟨rfl, rfl⟩
    norm_num