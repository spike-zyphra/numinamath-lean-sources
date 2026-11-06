import Mathlib

theorem number_theory_113120 (I M S : Set ℤ) (hI : I = ⊤) (hM : M = {x | ∃ n : ℤ, x = 2 * n})
    (hS : S = {x | ∃ n : ℤ, x = 3 * n}) :
    M ∩ (Sᶜ) = {x | ∃ n : ℤ, x = 6 * n + 2 ∨ x = 6 * n - 2} := by

  ext x
  simp only [hM, hS, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · -- Assume hM: (∃ k, x = 2 * k) ∧ hS: (∀ m, ¬x = 3 * m)
    rintro ⟨⟨k, hk⟩, h⟩
    have hk1 : x = 2 * k := by 
      linarith
    have h1 : (2 * k) % 3 = 1 ∨ (2 * k) % 3 = 2 := by
      by_contra h1
      push_neg at h1
      have h2 : (2 * k) % 3 = 0 := by 
        omega
      have h4 : ∃ m, x = 3 * m := by
        use (2 * k) / 3
        omega
      have h5 : ¬(∃ m, x = 3 * m) := by 
        simpa using h 
      contradiction 
    have h2 : k % 3 = 1 ∨ k % 3 = 2 := by 
      omega 
    rcases h2 with (h2 | h2)
    · -- Case k % 3 = 1.
      have hk4 : ∃ n, k = 3 * n + 1 := by
        refine' ⟨k / 3, by omega⟩
      rcases hk4 with ⟨n, hk5⟩
      use n 
      left
      linarith [hk5, hk1]
    · -- Case k % 3 = 2.
      have hk5 : ∃ m, k = 3 * m + 2 := by 
        refine' ⟨k / 3, by omega⟩
      rcases hk5 with ⟨m, hk6⟩
      use m + 1
      right 
      linarith [hk6, hk1]
  · -- Show that if x \in \{x \mid \exists n : \mathbb{Z}, x = 6 * n + 2 \lor x = 6 * n - 2 \}, then x in M \cap Sᶜ.
    rintro ⟨n, h⟩
    rcases h with (h | h)
    · -- x = 6 * n + 2
      constructor
      · -- Show x ∈ M.
        refine' ⟨3 * n + 1, by linarith⟩
      · -- Show x not in S.
        have eq1 : ¬ (∃ m, x = 3 * m) := by
          intro h_eqq
          rcases h_eqq with ⟨m, hm⟩
          have h1 : 6 * n + 2 = 3 * m := by 
            linarith [h, hm]
          omega 
        simpa using eq1 
    · -- x = 6 * n - 2
      constructor
      · -- Show x ∈ M.
        refine' ⟨3 * n - 1, by linarith⟩
      · -- Show x not in S.
        have eq1 : ¬ (∃ m, x = 3 * m) := by
          intro h_eqq
          rcases h_eqq with ⟨m, hm⟩
          have h1 : 6 * n - 2 = 3 * m := by 
            linarith [h, hm]
          omega 
        simpa using eq1