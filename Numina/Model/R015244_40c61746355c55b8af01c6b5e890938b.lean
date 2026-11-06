import Mathlib

theorem algebra_316376 {f : ℕ → ℕ}
    (h : ∀ x, 0 < x → (x > 1005 → f x = f (f (x - 7))) ∧ (x ≤ 1005 → f x = x + 3)) :
    f 2006 = 1005 := by
  set_option maxRecDepth 10000 in
  norm_num [h] at *
  <;> try { tauto }