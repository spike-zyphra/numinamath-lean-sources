import Mathlib

theorem algebra_11297 (a : Fin 5 ↪ ℕ) (ha0 : a 0 = 88) (ha1 : a 1 = 73) (ha2 : a 2 = 70)
    (hmean : (∑ i, a i) / (5 : ℚ) = 81) (hlt : ∀ i, a i < 90) :
    {a 3, a 4} = ({85, 89} : Set ℕ) := by
  have h1 : ∑ i, a i = 405 := by
    have h2 : (∑ i, (a i : ℚ)) = 405 := by
      have hmean' : (∑ i, (a i : ℚ)) / (5 : ℚ) = 81 := by
        simpa using hmean
      field_simp at hmean'
      linarith
    have h3 : (∑ i, (a i : ℕ) ) = 405 := by
      exact_mod_cast h2
    exact_mod_cast h3
  have h34sum : a 3 + a 4 = 174 := by
    have h5 : a 0 + a 1 + a 2 + a 3 + a 4 = 405 := by
      have h6 : ∑ i, a i = 405 := h1
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h6 ⊢
      <;> linarith
    linarith [ha0, ha1, ha2, h5]
  have h30 : a 3 ≠ 88 := by
    intro h
    have h40 : a 3 = a 0 := by
      rw [h, ha0]
    have h41 : (3 : Fin 5) = (0 : Fin 5) := by
      apply a.injective
      simpa using h40
    simp at h41
  have h300 : a 3 ≠ 73 := by
    intro h
    have h40 : a 3 = a 1 := by
      rw [h, ha1]
    have h41 : (3 : Fin 5) = (1 : Fin 5) := by
      apply a.injective
      simpa using h40
    simp at h41
  have h310 : a 3 ≠ 70 := by
    intro h
    have h40 : a 3 = a 2 := by
      rw [h, ha2]
    have h41 : (3 : Fin 5) = (2 : Fin 5) := by
      apply a.injective
      simpa using h40
    simp at h41
  have h400 : a 4 ≠ 88 := by
    intro h
    have h40 : a 4 = a 0 := by
      rw [h, ha0]
    have h41 : (4 : Fin 5) = (0 : Fin 5) := by
      apply a.injective
      simpa using h40
    simp at h41
  have h411 : a 4 ≠ 73 := by
    intro h
    have h40 : a 4 = a 1 := by
      rw [h, ha1]
    have h41 : (4 : Fin 5) = (1 : Fin 5) := by
      apply a.injective
      simpa using h40
    simp at h41
  have h422 : a 4 ≠ 70 := by
    intro h
    have h40 : a 4 = a 2 := by
      rw [h, ha2]
    have h41 : (4 : Fin 5) = (2 : Fin 5) := by
      apply a.injective
      simpa using h40
    simp at h41
  have h5 : (a 3 = 85 ∧ a 4 = 89) ∨ (a 3 = 89 ∧ a 4 = 85) := by
    have h11 : a 3 + a 4 = 174 := h34sum
    have h12 : a 3 < 90 := by apply hlt
    have h13 : a 4 < 90 := by apply hlt
    have h14 : a 3 ≠ a 4 := by
      intro h
      have h11 : (3 : Fin 5) = (4 : Fin 5) := by
        apply a.injective
        simpa using h
      simp at h11
    omega
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h5 with ⟨h85, h89⟩ | ⟨h89, h85⟩
  · -- Assume a 3 = 85 and a 4 = 89.
    rw [show a 3 = 85 by linarith, show a 4 = 89 by linarith]
    all_goals
      tauto
  · -- Assume a 3 = 89 and a 4 = 85.
    rw [show a 3 = 89 by linarith, show a 4 = 85 by linarith]
    all_goals
      tauto