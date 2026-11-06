import Mathlib


theorem algebra_177314 {m n : ℝ} {f : ℝ → ℝ}
    (hmnezero : m ≠ 0)
    (hm : m = 1) (hn : n = 0)
    (hf : ∀ x, f x = m * x + n) :
    {x | 2 * f x = f (x + 2)} = {2} := by

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]

  constructor
  · -- Assume 2 * f x = f (x + 2), prove x = 2
    intro h
    have h1 : f x = m * x + n := hf x
    have h2 : f (x + 2) = m * (x + 2) + n := hf (x + 2)
    rw [h1] at h
    rw [h2] at h
    rw [hm, hn] at h
    norm_num at h
    linarith

  · -- Assume x = 2, prove 2 * f x = f (x + 2)
    intro h
    rw [h]
    have h1 : f 2 = m * (2 : ℝ) + n := hf 2
    have h2 : f ( (2 : ℝ) + 2 ) = m * ( (2 : ℝ) + 2 ) + n := hf ( (2 : ℝ) + 2 )
    rw [h1, h2]
    rw [hm, hn]
    norm_num