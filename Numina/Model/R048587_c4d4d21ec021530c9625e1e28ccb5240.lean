import Mathlib

theorem algebra_154794 (f : ℝ → ℝ) (hf : f = fun x => 1 / x) :
    {x | x ≠ 0} = {x | x > 0} ∪ {x | x < 0} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_union]
        constructor
        · -- Assume x ≠ 0, we need to prove x > 0 ∨ x < 0
          intro h
          by_contra h'
          push_neg at h'
          have h1 : x ≤ 0 := by linarith
          have h2 : x ≥ 0 := by linarith
          have h3 : x = 0 := by linarith
          contradiction
        · -- Assume x > 0 ∨ x < 0, we need to prove x ≠ 0
          rintro (h | h)
          · -- Case x > 0
            by_contra h'
            rw [h'] at h
            linarith
          · -- Case x < 0
            by_contra h'
            rw [h'] at h
            linarith