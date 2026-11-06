import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11063 {f : ℝ → ℝ}
  (hf : ∀ x, x < -2 → f x = 2 * x + 7)
  (hf' : ∀ x, x ≥ -2 → f x = -x ^ 2 - x + 1) :
  ∑ᶠ x ∈ {x | f x = -5}, x = -4 := by
    have h1 : {x : ℝ | f x = -5} = {-6, 2} := by 
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Show that if f(x) = -5, then x ∈ {-6, 2}
        intro hfx
        by_cases h : x < -2
        · -- Case where x < -2
          have hfx1 : f x = 2 * x + 7 := hf x h
          rw [hfx1] at hfx
          have hx1 : x = -6 := by linarith
          rw [hx1]
          left
          norm_num
        · -- Case where x ≥ -2
          have h2 : x ≥ -2 := by linarith
          have hfx2 : f x = -x ^ 2 - x + 1 := hf' x h2
          rw [hfx2] at hfx
          have h_eq : x = 2 ∨ x = -3 := by
            have : -x ^ 2 - x + 1 = -5 := by linarith
            have h_eq : x ^ 2 + x - 6 = 0 := by 
              nlinarith
            have : (x - 2) * (x + 3) = 0 := by 
              nlinarith
            cases' (mul_eq_zero.mp this) with h3 h4
            · -- Case x - 2 = 0 
              left 
              linarith 
            · -- Case x + 3 = 0 
              right 
              linarith 
          cases h_eq with 
          | inl h_eq => 
            rw [h_eq]
            right 
            norm_num 
          | inr h_eq => 
            linarith 
      · -- Show that if x ∈ {-6, 2}, then f(x) = -5
        rintro (h | h)
        · -- Case x = -6
          rw [h]
          norm_num [hf]
        · -- Case x = 2
          rw [h]
          norm_num [hf']
    rw [h1]
    rw [finsum_mem_pair (by norm_num)]
    all_goals norm_num