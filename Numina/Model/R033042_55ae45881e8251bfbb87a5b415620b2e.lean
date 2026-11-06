import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_118259 {f g : ℝ → ℝ}
  (hf : f = λ x => if x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 then 5 * x - 3 else 0)
  (hg : g = λ x => if x = -2 ∨ x = -1 ∨ x = 1 ∨ x = 4 ∨ x = 5 then x ^ 2 - 2 * x - 3 else 0) :
  {x | 0 < f x ∧ 0 < g x} = {4, 5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hf, hg]
  constructor
  · -- Assume 0 < f x ∧ 0 < g x, show x ∈ {4, 5}
    intro h
    rcases h with ⟨hf_pos, hg_pos⟩
    by_cases hfx0 : x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5
    · -- Assume x is in {0, 2, 3, 4, 5}
      rw [if_pos hfx0] at hf_pos
      by_cases hgx0 : x = -2 ∨ x = -1 ∨ x = 1 ∨ x = 4 ∨ x = 5
      · -- Assume x is in {-2, -1, 1, 4, 5}
        rw [if_pos hgx0] at hg_pos
        have hx1 : x > (3 : ℝ) / 5 := by linarith 
        have hx2 : x ^ 2 - 2 * x - 3 > 0 := by nlinarith
        have h3 : x = 4 ∨ x = 5 := by
          rcases hfx0 with (r | r | r | r | r)
          · -- x = 0
            exfalso
            rw [r] at hx1
            norm_num at hx1
          · -- x = 2
            exfalso
            rw [r] at hx2
            norm_num at hx2
          · -- x = 3
            exfalso
            rw [r] at hx2
            norm_num at hx2
          · -- x = 4
            left
            linarith
          · -- x = 5
            right
            linarith
        tauto
      · -- Assume x is not in {-2, -1, 1, 4, 5}
        rw [if_neg hgx0] at hg_pos
        norm_num at hg_pos
    · -- Assume x is not in {0, 2, 3, 4, 5}
      rw [if_neg hfx0] at hf_pos
      norm_num at hf_pos
  · -- Assume x ∈ {4, 5}, show 0 < f x ∧ 0 < g x
    intro h
    rcases h with (r | r)
    · -- x = 4
      rw [r]
      constructor
      · -- Show 0 < f 4 
        norm_num
      · -- Show 0 < g 4 
        norm_num
    · -- x = 5 
      rw [r]
      constructor
      · -- Show 0 < f 5 
        norm_num
      · -- Show 0 < g 5 
        norm_num