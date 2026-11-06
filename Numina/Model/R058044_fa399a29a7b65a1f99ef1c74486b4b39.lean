import Mathlib

theorem algebra_156167 {a b : ℕ → ℝ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = a (n - 1) + (a (n - 1)) ^ 2 / a (n - 2))
    (hb0 : b 0 = 1) (hb1 : b 1 = 3)
    (hbn : ∀ n ≥ 2, b n = b (n - 1) + (b (n - 1)) ^ 2 / b (n - 2)) :
    b 32 / a 32 = 561 := by
  norm_num [ha0, ha1, han, hb0, hb1, hbn]
  <;> ring_nf <;> norm_num