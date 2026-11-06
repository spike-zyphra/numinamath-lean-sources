import Mathlib

theorem algebra_13898 {f : ℝ → ℝ}
    (hf : ∀ x, x ≤ 1 → f x = -x - 3)
    (hf' : ∀ x, x > 1 → f x = x / 2 + 1) :
    ∑ᶠ x ∈ {x | f x = 0}, x = -3 := by
  have h1 : {x : ℝ | f x = 0} = {-3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume f(x) = 0; we need to prove x = -3
      intro hx
      by_cases h : x ≤ 1
      · -- Case x ≤ 1: Then f(x) = -x - 3
        have hfx : f x = -x - 3 := hf x h
        rw [hfx] at hx
        linarith
      · -- Case x > 1: Then f(x) = x / 2 + 1
        have h2 : x > 1 := by linarith
        have hfx : f x = x / 2 + 1 := hf' x h2
        rw [hfx] at hx
        linarith -- This will derive a contradiction as x > 1 and x = -2 cannot both be true
    · -- Assume x = -3; we need to prove f(x) = 0
      intro hx
      rw [hx]
      have h : (-3 : ℝ) ≤ 1 := by norm_num
      rw [hf (-3) h]
      norm_num
  rw [h1]
  simp