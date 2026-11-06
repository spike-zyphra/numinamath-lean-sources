import Mathlib

theorem algebra_221635 {f g : ℝ → ℝ} (hf : Odd f) (hg : Even g)
    (hfg : ∀ x > 0, f x * g x < 0) (hfg' : g 3 = 0) :
    {x | f x * g x < 0} = {x | x < -3 ∨ x ∈ Set.Ioo 0 3} := by
  have h3 : (0 : ℝ) < (0 : ℝ) := by
    have h4 : f 3 * g 3 < (0 : ℝ) := hfg 3 (by norm_num)
    rw [hfg'] at h4
    nlinarith
  -- The hypotheses are contradictory, so the theorem is vacuously true.
  show {x | f x * g x < 0} = {x | x < -3 ∨ x ∈ Set.Ioo 0 3}
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioo]
  all_goals try { 
    exfalso
    all_goals try { linarith [h3] }
  }