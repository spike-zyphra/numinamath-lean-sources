import Mathlib

theorem algebra_277456 {f : ℕ → ℕ}
    (h : ∀ n, n ≥ 1000 → f n = n - 3)
    (h' : ∀ n, n < 1000 → f n = f (f (n + 7))) : f 90 = 999 := by 
  norm_num [h, h']
  <;> try { native_decide }