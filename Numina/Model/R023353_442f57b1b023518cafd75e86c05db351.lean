import Mathlib

theorem algebra_247867 {P : Polynomial ℤ} (hP : P.degree = 2022) (hP1 : P.coeff 2022 = 1) :
    {x | x ∈ Set.Ioo 0 1 ∧ P.eval x = 0}.encard ≤ 2021 := by
  have h3 : {x | x ∈ Set.Ioo 0 1 ∧ P.eval x = 0} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hn1, hn2⟩, h_eq⟩
    have h4 : n > 0 := by omega 
    have h5 : n < 1 := by omega 
    omega
  rw [h3]
  simp