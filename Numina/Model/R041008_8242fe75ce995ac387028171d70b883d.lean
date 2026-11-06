import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_14258 {f : ℝ → ℝ}
  (hf : ∀ x, x ≤ 0 → f x = -x + 3)
  (hf' : ∀ x, x > 0 → f x = 2 * x - 5) :
  {x | f (f x) = 4}.ncard = 3 := by
  have h1 : {x : ℝ | f (f x) = 4} = {-1.5, 2, 4.75} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- If f(f(x)) = 4, then x ∈ {-1.5, 2, 4.75}
      intro h
      by_cases h2 : f x ≤ 0
      · -- If f(x) ≤ 0, then f(f(x)) = - (f(x)) + 3.
        have h3 : f (f x) = - (f x) + 3 := hf (f x) h2
        rw [h3] at h
        have hfx1 : f x = -1 := by linarith
        by_cases h4 : x ≤ 0
        · -- If x ≤ 0, then f(x) = -x + 3.
          have hfx2 : f x = -x + 3 := hf x h4
          rw [hfx2] at hfx1
          have hx : x = (4 : ℝ) := by linarith
          nlinarith
        · -- x > 0
          have h5 : x > 0 := by linarith
          have hfx3 : f x = 2 * x - 5 := hf' x (by linarith)
          rw [hfx3] at hfx1
          have hx : x = (2 : ℝ) := by linarith
          right
          left
          norm_num at hx ⊢
          exact hx
      · -- If f(x) > 0, then f(f(x)) = 2 * (f(x)) - 5.
        have h2' : f x > 0 := by linarith
        have h4 : f (f x) = 2 * (f x) - 5 := hf' (f x) (by linarith)
        rw [h4] at h
        have hfx2 : f x = 4.5 := by linarith
        by_cases h5 : x ≤ 0
        · -- If x ≤ 0, then f(x) = -x + 3.
          have hfx3 : f x = - x + 3 := hf x h5
          rw [hfx3] at hfx2
          have hx : x = (-1.5 : ℝ) := by linarith
          norm_num at hx ⊢
          left
          exact hx
        · -- x > 0
          have h5' : x > 0 := by linarith
          have hfx4 : f x = 2 * x - 5 := hf' x (by linarith)
          rw [hfx4] at hfx2
          have hx : x = (4.75 : ℝ) := by linarith
          right
          right
          norm_num at hx ⊢
          exact hx
    · -- If x ∈ {-1.5, 2, 4.75}, then f(f(x)) = 4
      rintro (rfl | rfl | rfl)
      · -- x = -1.5
        norm_num [hf, hf']
      · -- x = 2
        norm_num [hf, hf']
      · -- x = 4.75
        norm_num [hf, hf']
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> norm_num