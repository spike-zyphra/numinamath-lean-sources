import Mathlib

theorem algebra_14094 : IsGreatest {x : ℕ | x * 14 * (1 + 5 / 100 : ℝ) + 2 ≤ 130} 8 := by 
  constructor 
  · -- Show that 8 is indeed in the set.
    show (8 : ℕ) ∈ {x : ℕ | x * 14 * (1 + 5 / 100 : ℝ) + 2 ≤ 130}
    simp only [Set.mem_setOf_eq]
    norm_num 
  · -- Show that 8 is the greatest element in the set 
    intro x 
    intro h 
    have h1 : (x : ℕ) ∈ {x : ℕ | x * 14 * (1 + 5 / 100 : ℝ) + 2 ≤ 130} := h 
    simp only [Set.mem_setOf_eq] at h1
    by_contra h2 
    push_neg at h2 
    have h2' : x ≥ 9 := by linarith 
    have h2 : (x : ℝ) ≥ (9 : ℝ) := by exact_mod_cast h2' 
    norm_num at h1 
    linarith