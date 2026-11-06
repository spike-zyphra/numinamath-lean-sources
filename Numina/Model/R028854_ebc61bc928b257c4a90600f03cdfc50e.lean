import Mathlib

theorem number_theory_277641:
  IsLeast {n:ℕ | n % 9 = 8 ∧ Odd n ∧ n ∈ Finset.Icc 1000 9999 ∧
  (∃ (a b c d: Fin 10), n = 1000*(a:ℕ) + 100*(b:ℕ) + 10*(c:ℕ) + (d:ℕ) ∧
    1000*(c:ℕ) + 100*(d:ℕ) + 10*(a:ℕ) + b = n + 5940) } 1979 := by
  constructor
  · -- Show 1979 is in the set
    constructor
    · norm_num
    constructor
    · use 989
      all_goals norm_num
    constructor
    · norm_num [Finset.mem_Icc]
    · -- Show ∃ (a b c d: Fin 10), 1979 = 1000*(a:ℕ) + 100*(b:ℕ) + 10*(c:ℕ) + (d:ℕ) ∧
      -- 1000*(c:ℕ) + 100*(d:ℕ) + 10*(a:ℕ) + b = 1979 + 5940
      use 1, 9, 7, 9
      simp
      <;> try { native_decide }
      all_goals try { native_decide }
  · -- Show that 1979 is the least
    intro n hn
    rcases hn with ⟨h1, h2, h3, h4⟩
    rw [Finset.mem_Icc] at h3
    rcases h4 with ⟨a, b, c, d, h_eq1, h_eq2⟩
    simp [Odd] at h2
    norm_num at h3 ⊢
    try { omega }
    all_goals try { native_decide }