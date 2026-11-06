import Mathlib

def a : ℕ → ℕ
| n => n ^ 2 + n + 2

theorem number_theory_304416 :
    {n | ∃ m, a n = m ^ 2}.Finite := by
  have h1 : {n | ∃ m, a n = m ^ 2} = {1} := by
    ext n
    simp [a]
    constructor
    · -- Assume h : ∃ m, a n = m ^ 2
      rintro ⟨m, hm⟩
      by_cases h2 : n > 1
      · -- Assume n > 1
        have h3 : n ≥ 2 := by omega
        have h4 : m < n + 1 := by 
          nlinarith [hm, h3]
        have h5 : m > n := by
          nlinarith [hm, h3]
        omega -- contradiction of $m >n$ and $m <n+1$
      · -- Assume ¬(n > 1)
        have h8 : n ≤ 1 := by omega
        have : n = 0 ∨ n = 1 := by omega
        rcases this with (h | h)
        · -- n = 0
          rw [h] at hm
          norm_num at hm
          have h9 : m ≤ 2 := by
            nlinarith
          interval_cases m <;> omega 
        · -- n = 1
          omega 
    · -- Assume h : n = 1
      intro h
      rw [h]
      use 2
      all_goals norm_num [a]
  rw [h1]
  apply Set.toFinite