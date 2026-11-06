import Mathlib

theorem number_theory_167921 :
    IsLeast {x : ℕ | 0 < x ∧ ∀ n : ℕ, Odd n → 1984 ∣ 47^n + x * 15^n} 1055 := by 
  constructor
  · -- Show that 1055 is in the set.
    constructor
    · norm_num
    · -- Show that for all odd n, 1984 divides 47^n + 1055 * 15^n
      intro n hn
      have h1 : ∀ (k : ℕ), 1984 ∣ 47 ^ (2 * k + 1) + 1055 * 15 ^ (2 * k + 1) := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          norm_num [pow_succ, pow_mul] at ih ⊢
          <;> ring_nf at ih ⊢
          <;> omega
      have h2 : ∃ k : ℕ, n = 2 * k + 1 := by
        obtain ⟨k, hk⟩ := hn
        use k
        all_goals linarith [hk]
      rcases h2 with ⟨k, hk⟩
      rw [hk]
      apply h1 k
  · -- Show that 1055 is the least in the set.
    intro x hx
    rcases hx with ⟨hx_pos, hx_prop⟩
    by_contra h
    push_neg at h
    have h1 := hx_prop 1 (by decide)
    norm_num at h1
    interval_cases x <;> omega