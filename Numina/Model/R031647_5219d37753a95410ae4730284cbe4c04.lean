import Mathlib

theorem algebra_286710 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + 2 * y = 2008) (hmax : ∀ x' y' : ℕ, 0 < x' → 0 < y' → x' + 2 * y' = 2008 → x * y ≥ x' * y') :
    x - y = 502 := by

  have h1 := hmax 1004 502 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1
  have h2 : x = 1004 := by
    nlinarith [sq_nonneg ((x : ℕ) - 1004 : ℤ), sq_nonneg ((y : ℕ) - 502 : ℤ),
      hxy, h1, mul_pos hx hy]
  have h3 : y = 502 := by
    linarith [h2, hxy]
  calc
    x - y = 1004 - 502 := by rw [h2, h3]
    _ = 502 := by omega