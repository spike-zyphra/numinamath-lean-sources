import Mathlib

theorem number_theory_19441
    (a b : ℕ → ℕ)
    (ha0 : a 0 = 0)
    (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = a (n - 1) + b (n - 2))
    (hb0 : b 0 = 1)
    (hb1 : b 1 = 2)
    (hbn : ∀ n ≥ 2, b n = a (n - 2) + b (n - 1)) :
    (a 50 + b 50) % 5 = 4 := by
  norm_num [ha0, ha1, han, hb0, hb1, hbn]
  <;> try { omega }