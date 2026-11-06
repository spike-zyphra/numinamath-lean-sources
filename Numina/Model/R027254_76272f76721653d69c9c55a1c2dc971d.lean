import Mathlib

theorem number_theory_222730 (a : Fin 2002 → ℤ) :
    (∑ i : Fin 2002, a i) % 6 = 0 → (∑ i : Fin 2002, (a i)^3) % 6 = 0 := by
  intro h
  have h1 : ∀ x : ℤ, (x ^ 3) % 6 = x % 6 := by
    intro x
    have h2 : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2)
    · -- Case where $x \equiv 0 \pmod{6}$
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero]
    · -- Case where $x \equiv 1 \pmod{6}$
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero]
    · -- Case where $x \equiv 2 \pmod{6}$
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero]
    · -- Case where $x \equiv 3 \pmod{6}$
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero]
    · -- Case where $x \equiv 4 \pmod{6}$
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero]
    · -- Case where $x \equiv 5 \pmod{6}$
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero]

  have h4 : (∑ i : Fin 2002, (a i)^3) % 6 = (∑ i : Fin 2002, a i) % 6 := by 
    simp [Finset.sum_int_mod, h1]
  rw [h4] 
  exact h