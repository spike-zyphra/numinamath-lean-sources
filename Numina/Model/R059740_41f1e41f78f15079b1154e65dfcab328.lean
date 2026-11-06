import Mathlib

theorem algebra_12001 {f : ℝ → ℝ} (hf : ∀ x, x < 2 → f x = 9 * x + 16)
    (hf' : ∀ x, x ≥ 2 → f x = 2 * x - 14) :
    ∑ᶠ x ∈ {x | f x = -2}, x = 4 := by
  have h1 : {x | f x = -2} = {-2, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume f(x) = -2
      intro hfx
      by_cases h : x < 2
      · -- If x < 2, then f(x) = 9x + 16
        have hfx1 : f x = 9 * x + 16 := hf x h
        rw [hfx1] at hfx
        left
        linarith
      · -- Case x ≥ 2
        have h' : x ≥ 2 := by linarith
        have hfx2 : f x = 2 * x - 14 := hf' x h'
        rw [hfx2] at hfx
        right
        linarith
    · -- Assume x ∈ {-2, 6}
      rintro (rfl | rfl)
      · -- x = -2
        norm_num [hf]
      · -- x = 6
        norm_num [hf']
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num