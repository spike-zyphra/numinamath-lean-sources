import Mathlib

theorem algebra_604096 {f : ℕ → ℕ}
    (hf : ∀ n, n > 0 → (n ≥ 1000 → f n = n - 3) ∧ (n < 1000 → f n = f (f (n + 7)))) :
    f 90 = 999 := by
  set_option maxRecDepth 20000 in
  norm_num [hf]