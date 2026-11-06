import Mathlib

theorem number_theory_154126 :
    ∃ j : Fin 3 → ℕ,
      (∀ i, j i > 0) ∧
      (∃ k : ℤ, (j 0 + j 1 + j 2) / 3 = k) ∧
      ¬∃ p : Equiv.Perm (Fin 3), ∀ i, j i = p i := by 
  use (fun _ => 1)
  constructor
  · -- Show all entries are positive
    intro i
    simp
  constructor
  · -- Show that the average is integer
    use 1
    simp
    <;> omega
  · -- Show that there is no permutation p
    intro h
    rcases h with ⟨p, hp⟩
    have hp0 := hp 0
    have hp1 := hp 1
    have hp2 := hp 2
    simp [Fin.sum_univ_three] at hp0 hp1 hp2
    have h01 : p 0 = p 1 := by
      omega
    have h_injective := p.injective
    have h' := h_injective h01
    simp [Fin.ext_iff] at h'
    all_goals omega