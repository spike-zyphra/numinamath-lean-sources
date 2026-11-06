import Mathlib

/-
Let $a,$ $b,$ and $c$ be distinct complex numbers such that
\begin{align*}
a^3 &= 2a + 5, \\
b^3 &= 2b + 5, \\
c^3 &= 2c + 5.
\end{align*}Find $a^3 + b^3 + c^3.$
-/
theorem algebra_22451 (a b c : ℂ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h1 : a^3 = 2 * a + 5) (h2 : b^3 = 2 * b + 5) (h3 : c^3 = 2 * c + 5) :
    a^3 + b^3 + c^3 = 15 := by
    let poly : Polynomial ℂ := Polynomial.X ^ 3 - Polynomial.C 2 * Polynomial.X - Polynomial.C 5
    let roots : Multiset ℂ := Multiset.ofList [a, b, c]

    have roots_card_eq_3: Multiset.card roots = 3 := by simp [roots]
    -- prove that poly has degree 3 and roots a, b, c
    have poly_ne_zero : poly ≠ 0 := by
      intro h
      have eval_zero : Polynomial.eval 0 poly = Polynomial.eval 0 0 := by rw [h]
      simp at eval_zero
      simp [poly] at eval_zero
    have poly_nat_degree_eq_three : poly.natDegree = 3 := by
      simp [poly]
      have h1: ((Polynomial.X : Polynomial ℂ) ^ 3).natDegree = 3 := by simp
      have h2: ( Polynomial.C 2 * (Polynomial.X : Polynomial ℂ)).natDegree = 1 := by rw [Polynomial.natDegree_C_mul]; simp; simp
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      exact h1
      rw [h1, h2]
      simp
    have roots_nodup : roots.Nodup := by
      rw [Multiset.nodup_iff_pairwise]
      unfold Multiset.Pairwise
      use [a, b, c]
      simp
      constructor
      constructor
      exact ha
      exact hc
      exact hb
    -- prove that roots are subset of roots of poly
    have roots_subset_p_roots: roots ⊆ poly.roots := by
      rw [Multiset.subset_iff]
      intro x x_in_roots
      simp [roots] at x_in_roots
      rw [Polynomial.mem_roots, Polynomial.IsRoot.def]
      simp [poly]
      match x_in_roots with
      | Or.inl x_eq_a => {rw [x_eq_a, h1];simp}
      | Or.inr (Or.inl x_eq_b) => {rw [x_eq_b, h2];simp}
      | Or.inr (Or.inr x_eq_c) => {rw [x_eq_c, h3];simp}
      exact poly_ne_zero
    have roots_le_p_roots: roots ≤ poly.roots := (Multiset.le_iff_subset roots_nodup).2 roots_subset_p_roots
    have roots_card_eq_p_roots_card : Multiset.card poly.roots = Multiset.card roots := by
      have roots_card_le_p_roots_card : Multiset.card poly.roots ≤ poly.natDegree := Polynomial.card_roots' poly
      rw [poly_nat_degree_eq_three] at roots_card_le_p_roots_card
      have roots_card_ge_three : Multiset.card roots ≤ Multiset.card poly.roots := Multiset.card_le_card roots_le_p_roots
      rw [roots_card_eq_3] at roots_card_ge_three
      rw [roots_card_eq_3]
      linarith
    have roots_eq_p_roots : roots = poly.roots := Multiset.eq_of_le_of_card_le roots_le_p_roots (le_of_eq roots_card_eq_p_roots_card)

    -- use vieta's formula
    have a_b_c_sum := Polynomial.coeff_eq_esymm_roots_of_card (
      show Multiset.card poly.roots = poly.natDegree by rw [roots_card_eq_p_roots_card, roots_card_eq_3, poly_nat_degree_eq_three])
      (show 2 ≤ poly.natDegree by rw [poly_nat_degree_eq_three]; linarith)
    rw [<- roots_eq_p_roots, poly_nat_degree_eq_three] at a_b_c_sum
    simp [poly, roots] at a_b_c_sum
    unfold Multiset.esymm Multiset.powersetCard at a_b_c_sum
    simp at a_b_c_sum
    match a_b_c_sum with
    | Or.inl h => exfalso; exact poly_ne_zero h
    | Or.inr h =>
      rw [h1, h2, h3]
      calc 2 * a + 5 + (2 * b + 5) + (2 * c + 5) = 2 * (c + (b + a)) + 15 := by ring
           _ = 2 * 0 + 15 := by rw [h]
            _ = 15 := by ring
