import Mathlib


/- Let $p$ be the least prime number for which there exists a positive integer $n$ such that $n^{4}+1$ is divisible by $p^{2}$. Find the least positive integer $m$ such that $m^{4}+1$ is divisible by $p^{2}$. -/
theorem number_theory_42608 (p : ℕ) (hp_least : IsLeast {p | p.Prime ∧ ∃ m, p ^ 2 ∣ m ^ 4 + 1} p) :
    IsLeast {m | 0 < m ∧ p ^ 2 ∣ m ^ 4 + 1} 110 := by
  -- Firstly, if there exists m such that p^2 | m^4 + 1, then specifically
  -- there exists such m with m < p^2.
  have h_dvd (n : ℕ) (hn : 0 < n) : (∃ m, n ∣ m ^ 4 + 1) ↔ (∃ m < n, n ∣ m ^ 4 + 1) := by
    constructor <;> rintro ⟨m, hm⟩
    · refine ⟨m % n, ⟨Nat.mod_lt m hn, ?_⟩⟩
      have : m ^ 4 + 1 ≡ (m % n) ^ 4 + 1 [ZMOD (n : ℤ)] := by
        gcongr
        exact (Int.mod_modEq m n).symm
      rw [Int.ModEq] at this
      norm_cast at this
      rwa [Nat.dvd_iff_mod_eq_zero.mp hm, eq_comm, ← Nat.dvd_iff_mod_eq_zero] at this
    · exact ⟨m, hm.right⟩

  -- Now since p is the least prime number satifying the condition given with m = 110 and 17 is one
  -- such prime, we know p ≤ 17.
  rw [IsLeast, Set.mem_setOf, lowerBounds, Set.mem_setOf] at hp_least ⊢
  obtain ⟨hp, hp_least⟩ := hp_least
  have hp_le : p ≤ 17 := by
    apply hp_least
    simp
    exact ⟨by decide, ⟨110, by decide⟩⟩

  -- From this, we can prove p = 17 exactly: for each other prime p < 17, enumerate all candidates
  -- of m < p ^ 2 and show the relation does not hold.
  have hp_eq : p = 17 := by
    apply eq_of_le_of_not_lt hp_le
    intro hp_lt
    specialize h_dvd (p ^ 2)
    interval_cases p
    · simp at hp
    · norm_num at hp
    all_goals
      specialize h_dvd (by decide)
      rw [h_dvd] at hp
      contrapose! hp
      native_decide

  -- Finally, it suffices to show that m = 110 is the smallest solution to 17 ^ 2 | m ^ 4 + 1. We do
  -- so by enumerating solutions.
  subst hp_eq
  constructor
  · decide
  · intro a ha
    contrapose! ha
    simp only [Nat.reducePow, Set.mem_setOf_eq, not_and]
    intro ha'
    interval_cases a <;> decide