import Mathlib

theorem number_theory_284228 :
    {u : ℤ | ∃ m n l : ℤ, u = 12 * m + 8 * n + 4 * l} =
      {u : ℤ | ∃ p q r : ℤ, u = 20 * p + 16 * q + 12 * r} := by 
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume u in M, prove in N
    rintro ⟨m, n, l, h⟩
    -- First we show that `u` is divisible by 4.
    have h1 : u % 4 = 0 := by 
      omega
    have h2 : ∃ k : ℤ, u = 4 * k := by
      refine' ⟨u / 4, by omega⟩
    rcases h2 with ⟨k, hk⟩
    have h3 : ∃ p q r : ℤ, u = 20 * p + 16 * q + 12 * r := by
      use 0, -2*k, 3*k
      all_goals 
        omega
    tauto
  · -- Assume u in N, prove in M
    rintro ⟨p, q, r, h⟩
    -- First we show that `u` is divisible by 4.
    have h1 : u % 4 = 0 := by 
      omega
    have h2 : ∃ k : ℤ, u = 4 * k := by
      refine' ⟨u / 4, by omega⟩
    rcases h2 with ⟨k, hk⟩
    have h4 : ∃ m n l : ℤ, u = 12 * m + 8 * n + 4 * l := by 
      use p, q, 2*p + 2*q + 3*r
      all_goals 
        omega
    tauto