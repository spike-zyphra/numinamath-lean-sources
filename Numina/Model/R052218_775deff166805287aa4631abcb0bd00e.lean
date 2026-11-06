import Mathlib

theorem number_theory_263107 :
    {n : ℕ | n ∈ [222, 2222, 22222, 222222] ∧ 3 ∣ n}.encard = 2 := by
  have h1 : {n : ℕ | n ∈ [222, 2222, 22222, 222222] ∧ 3 ∣ n} = {222, 222222} := by
    ext n
    simp [Nat.dvd_iff_mod_eq_zero]
    omega
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  <;> try linarith