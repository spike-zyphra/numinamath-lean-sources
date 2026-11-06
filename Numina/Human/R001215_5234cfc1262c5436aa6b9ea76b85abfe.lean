import Mathlib

open Polynomial

/- Let $a, b, c$ be distinct complex numbers such that \[\begin{aligned} 2a^3 + 7a^2 - 8a + 5 &= 0, \\ 2b^3 + 7b^2 - 8b + 5 &= 0, \\ 2c^3 + 7c^2 - 8c + 5 &= 0. \end{aligned}\]Compute the value of the product $abc.$ -/
theorem algebra_21549 {a b c : ℂ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h1 : 2*a^3+7*a^2-8*a+5=0) (h2 : 2*b^3+7*b^2-8*b+5=0) (h3 : 2*c^3+7*c^2-8*c+5=0) :
    a*b*c=-5/2 := by
  -- the product of the roots of a cubic polynomial is the negation of the constant term divided by the leading coefficient
  have eval_eq_prod_roots_sub_of_splits_id (p : ℂ[X])
    (hsplit : Splits (RingHom.id ℂ) p) (v : ℂ) :
    eval v p = p.leadingCoeff * (p.roots.map fun a ↦ v - a).prod := by
    have aeval_eq_prod_aroots_sub_of_splits [Algebra ℂ ℂ] {p : ℂ[X]}
    (hsplit : Splits (algebraMap ℂ ℂ) p) (v : ℂ) :
    aeval v p = algebraMap ℂ ℂ p.leadingCoeff * ((p.aroots ℂ).map fun a ↦ v - a).prod := by
      rw [← eval_map_algebraMap, eq_prod_roots_of_splits hsplit]
      simp [eval_multiset_prod]
    convert aeval_eq_prod_aroots_sub_of_splits hsplit v
    rw [Algebra.id.map_eq_id, map_id]
  have vieta := eval_eq_prod_roots_sub_of_splits_id (C 2*X^3 + C 7*X^2 + C (-8)*X + C 5) (by exact IsAlgClosed.splits _) 0
  simp only [map_neg, neg_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, eval_neg, neg_zero, zero_add, zero_sub, Multiset.prod_map_neg] at vieta
  -- the leading coefficient of the polynomial $2x^3 + 7x^2 - 8x + 5$ is 2
  have leadcoe := @leadingCoeff_cubic ℂ 2 7 (-8) 5 _ (by exact Ne.symm (NeZero.ne' 2))
  simp only [map_neg, neg_mul] at leadcoe
  -- $2x^3 + 7x^2 - 8x + 5 \neq 0$
  have pne : (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5 : ℂ[X]) ≠ 0 := by
    by_contra contra
    rw [contra] at leadcoe
    simp only [leadingCoeff_zero, OfNat.zero_ne_ofNat] at leadcoe
  rw [leadcoe] at vieta
  -- the polynomial $2x^3 + 7x^2 - 8x + 5$ has 3 roots
  have cardroots : Multiset.card (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5 : ℂ[X]).roots = 3 := by
    have degeq :=@natDegree_cubic ℂ 2 7 (-8) 5 _ (by exact Ne.symm (NeZero.ne' 2))
    simp only [map_neg, neg_mul] at degeq
    have : Multiset.card (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5 : ℂ[X]).roots = (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5: ℂ[X]).natDegree := by
      have eq := @natDegree_eq_card_roots ℂ ℂ _ _ (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5) (by exact RingHom.id ℂ) (by exact IsAlgClosed.splits _)
      rw [eq]
      simp only [Polynomial.map_add, Polynomial.map_mul, map_C, RingHom.id_apply, Polynomial.map_pow, map_X, Polynomial.map_neg]
    rw [this, degeq]
  rw [cardroots] at vieta
  norm_num at vieta
  -- the roots of the polynomial $2x^3 + 7x^2 - 8x + 5$ are $a, b, c$
  have rootseq : (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5 : ℂ[X]).roots = {a, b, c} := by
    -- $a, b, c$ are roots
    have subset : {a, b, c} ⊆ (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5 : ℂ[X]).roots := by
      intro x xin
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at xin
      rcases xin with xeq | xeq | xeq
      -- $a$ is a root
      rw [xeq]
      simp only [mem_roots', ne_eq, IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_neg]
      constructor
      exact pne
      rw [← sub_eq_add_neg]
      exact h1
      -- $b$ is a root
      rw [xeq]
      simp only [mem_roots', ne_eq, IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_neg]
      constructor
      exact pne
      rw [← sub_eq_add_neg]
      exact h2
      -- $c$ is a root
      rw [xeq]
      simp only [mem_roots', ne_eq, IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_neg]
      constructor
      exact pne
      rw [← sub_eq_add_neg]
      exact h3
    -- the multiset $\{a, b, c\}$ is less than or equal to the multiset of roots
    have le : {a, b, c} ≤ (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5 : ℂ[X]).roots := by
      refine (Multiset.le_iff_subset ?_).mpr subset
      simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons, ha, Multiset.mem_singleton, hc, or_self, not_false_eq_true, hb, Multiset.nodup_singleton, and_self]
    -- the cardinality multiset of roots is less than or equal to that of $\{a, b, c\}$
    have card : Multiset.card (C 2 * X ^ 3 + C 7 * X ^ 2 + -(C 8 * X) + C 5 : ℂ[X]).roots ≤ Multiset.card {a, b, c} := by
      rw [cardroots]
      simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton, Nat.reduceAdd]
      linarith
    exact Eq.symm (Multiset.eq_of_le_of_card_le le card)
  -- the product of the roots of the polynomial $2x^3 + 7x^2 - 8x + 5$ is $abc$
  rw [rootseq] at vieta
  simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton] at vieta
  -- $abc = -5/2$
  rw [← mul_assoc a] at vieta
  symm at vieta
  apply congrArg (fun x ↦ -x / 2) at vieta
  ring_nf at vieta
  exact vieta
  