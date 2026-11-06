import Mathlib

/- 5. Is it possible to arrange the numbers from 1 to 30 in a circle so that the sum of any two adjacent numbers is equal to the square of some natural number? -/
theorem number_theory_286882 :
    ¬∃ f : Fin 30 → Fin 30,
      Function.Bijective f ∧
      (∀ i, ∃ n:ℕ , ↑(f i) + ↑(f (i + 1)) = n ^ 2) := by
  intro h
  obtain ⟨f, ⟨ h_inj, h_surj ⟩, h_sum⟩ := h
  obtain ⟨ x, h_x ⟩ := h_surj 18
  -- the only possible value for the neighbour of 18 is 7
  have (a : Fin 30) (h : ∃ n:ℕ, ↑a + 18 = n^2) (h_neq : a ≠ 18) : a = 7 := by
    obtain ⟨ n, h⟩ := h
    suffices : n < 7
    . interval_cases n <;> omega
    have : (a:ℕ) + 18 < 49 := calc
      ↑a + 18 < 30 + 18 := by
        apply (add_lt_add_iff_right 18).mpr
        apply Fin.isLt
      _ < 49 := by simp
    rw [h] at this
    by_contra h_le
    simp at h_le
    have : n^2 ≥ 49 :=
      calc n^2 = n*n := sq n
      _ ≥ 7 * 7 := by apply Nat.mul_le_mul h_le h_le
    linarith
  have h_neq_18 (y:Fin 30) (h_neq_x : y ≠ x) : f y ≠ 18 := by
    intro h
    apply h_neq_x
    apply h_inj
    rw [h_x, h]
  -- The number 18 should have two neighbours, so it is impossible to arrange the numbers without repetition
  have h₁ : f (x-1) = 7 := by
    apply this
    case h_neq =>
      apply h_neq_18
      omega
    specialize h_sum (x-1)
    obtain ⟨n, h⟩ := h_sum
    use n
    rw [← h]
    simp
    rw [h_x]
    trivial
  have h₂ : f (x+1) = 7 := by
    apply this
    case h_neq =>
      apply h_neq_18
      omega
    specialize h_sum x
    obtain ⟨n, h⟩ := h_sum
    use n
    rw [← h, h_x, add_comm]
    trivial
  unfold Function.Injective at h_inj
  rw [← h₂] at h₁ 
  specialize h_inj h₁ 
  omega