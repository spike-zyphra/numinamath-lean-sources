import Mathlib

theorem number_theory_7185 : {x : ℤ | 1234 ≤ x ∧ x < 2014 ∧ 3 ∣ x}.encard = 260 := by 
  have h1 : {x : ℤ | 1234 ≤ x ∧ x < 2014 ∧ 3 ∣ x} = Finset.filter (λ x => 3 ∣ x) (Finset.Icc (1234 : ℤ) (2013 : ℤ)) := by
    ext x
    simp
    omega 
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide