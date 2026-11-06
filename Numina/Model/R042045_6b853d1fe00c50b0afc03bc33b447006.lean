import Mathlib

theorem number_theory_180149 : IsGreatest {x | ¬∃ n m, x = 3 * n + 7 * m} 11 := by
  constructor
  · -- Show 11 is in the set
    show ¬∃ n m, 11 = 3 * n + 7 * m
    rintro ⟨n, m, h⟩
    have h1 : 3 * n + 7 * m = 11 := by
      omega
    have h2 : m ≤ 1 := by
      omega
    interval_cases m <;> omega
  · -- Show there's no greater element in the set
    intro x hx
    by_contra h
    push_neg at h
    have h2 : ∃ n m, x = 3 * n + 7 * m := by
      have h3 : x > 11 := h
      have h4 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
        omega
      rcases h4 with (h | h | h)
      · -- Case 1: x % 3 = 0
        refine ⟨x / 3, 0, by omega⟩
      · -- Case 2: x % 3 = 1
        refine ⟨(x - 7) / 3, 1, by omega⟩
      · -- Case 3: x % 3 = 2
        refine ⟨(x - 14) / 3, 2, by omega⟩
    have h3 : ¬ ∃ n m, x = 3 * n + 7 * m := by 
      simpa using hx
    contradiction