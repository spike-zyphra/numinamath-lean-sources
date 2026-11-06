import Mathlib
open Mathlib
/-- Let $f(x)$ be a third-degree polynomial with real coefficients satisfying\[|f(1)|=|f(2)|=|f(3)|=|f(5)|=|f(6)|=|f(7)|=12.\]Find $|f(0)|$. -/
theorem algebra_85877 {f : Polynomial ℝ} (hf : f.degree = 3)
(h1 : |f.eval 1| = 12) (h2 : |f.eval 2| = 12) (h3 : |f.eval 3| = 12)
(h4 : |f.eval 5| = 12) (h5 : |f.eval 6| = 12) (h6 : |f.eval 7| = 12) :
|f.eval 0| = 72 := by
  -- expand all polynomials
  have a1 := eq_or_eq_neg_of_abs_eq h1
  have a2 := eq_or_eq_neg_of_abs_eq h2
  have a3 := eq_or_eq_neg_of_abs_eq h3
  have a4 := eq_or_eq_neg_of_abs_eq h4
  have a5 := eq_or_eq_neg_of_abs_eq h5
  have a6 := eq_or_eq_neg_of_abs_eq h6
  have gg : f.natDegree = 3 := by exact Polynomial.natDegree_eq_of_degree_eq_some hf
  simp only [Polynomial.eval_eq_sum_range, Finset.range, gg, Nat.reduceAdd, Multiset.range_succ,
    Multiset.range_zero, Multiset.cons_zero, Finset.mk_cons, Finset.cons_eq_insert, one_pow,
    mul_one, Finset.mem_insert, Nat.succ_ne_self, OfNat.ofNat_ne_one, Finset.mem_mk,
    Multiset.mem_singleton, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert,
    one_ne_zero, Finset.sum_mk, Multiset.map_singleton, Multiset.sum_singleton, pow_one,
    pow_zero] at a1 a2 a3 a4 a5 a6
  norm_num at *
  have jej := Polynomial.coeff_ne_zero_of_eq_degree hf
  simp only [Polynomial.eval, Polynomial.eval₂_at_zero, RingHom.id_apply]
  obtain a1 | a1 := a1
  all_goals obtain a2 | a2 := a2
  all_goals obtain a3 | a3 := a3
  all_goals obtain a4 | a4 := a4
  all_goals obtain a5 | a5 := a5
  all_goals obtain a6 | a6 := a6
  all_goals try linarith -- By drawing a coordinate axis, and two lines representing $12$ and $-12$, it is easy to see that $f(1)=f(5)=f(6)$, and $f(2)=f(3)=f(7)$; otherwise more bends would be required in the graph.
  all_goals (try (rw [(by linarith : f.coeff 0 = 72)]; norm_num)) -- a = 72
  all_goals (try (rw [(by linarith : f.coeff 0 = -72)]; norm_num)) -- a = -72
  all_goals exact False.elim (jej (by linarith)) -- this is not a 3rd degree polynomial