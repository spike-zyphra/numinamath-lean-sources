import Mathlib


theorem algebra_177314 {m n : ℝ} {f : ℝ → ℝ}
    (hmnezero : m ≠ 0)
    (hm : m = 1) (hn : n = 0)
    (hf : ∀ x, f x = m * x + n) :
    {x | 2 * f x = f (x + 2)} = {2} := by

  simp_rw [hm, hn, one_mul, add_zero] at hf

  ext x
  simp_rw [hf, Set.mem_setOf_eq, Set.mem_singleton_iff]

  constructor

  . exact fun hx => (by linarith only [hx])

  . exact fun hx => (by norm_num [hx])
