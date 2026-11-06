import Mathlib

theorem algebra_248436 {P : Polynomial ℂ} (n : ℕ) (hP : P.degree = n) :
    Set.ncard {z : ℂ | P.eval z = 0} ≤ n := by
  have h10 : P ≠ 0 := by
    by_contra h
    rw [h] at hP
    simp at hP
  have h4 : {z : ℂ | P.eval z = 0} = P.roots.toFinset := by
    ext z
    simp [Polynomial.mem_roots, h10]
  rw [h4]
  have h5 : P.roots.card ≤ P.natDegree := by
    apply Polynomial.card_roots'
  have h6 : (P.roots.toFinset).card ≤ P.roots.card := by
    apply Multiset.toFinset_card_le
  have h7 : P.natDegree = n := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
  have h8 : (P.roots.toFinset).card ≤ n := by
    have h9 : (P.roots.toFinset).card ≤ P.roots.card := h6
    have h10 : P.roots.card ≤ P.natDegree := h5
    have h11 : P.natDegree = n := h7
    linarith
  rw [Set.ncard_coe_Finset]
  linarith