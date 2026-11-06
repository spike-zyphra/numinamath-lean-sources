import Mathlib

theorem number_theory_10979 : IsLeast {n : ℕ+ | 4 * n.val % 11 = 0} 11 := by
  constructor
  · -- Show 11 is in the set
    show 4 * (11 : ℕ+).val % 11 = 0
    simp
  · -- Show there is no smaller element in the set
    intro n hn
    have h : 4 * n.val % 11 = 0 := hn
    have h1 : n.val ≥ 11 := by
      by_contra h2
      push_neg at h2
      have h3 : n.val < 11 := h2
      have h4 : n.val > 0 := by
        exact n.prop
      interval_cases h5 : n.val <;> norm_num at h
    have h2 : (n : ℕ+).val ≥ 11 := h1
    exact h2