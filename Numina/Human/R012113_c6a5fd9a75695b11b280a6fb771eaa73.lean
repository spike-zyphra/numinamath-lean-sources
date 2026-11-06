import Mathlib

open affineSpan

/- Lemma 1: If f satisfies the given functional equation, then the points (x, f x), (y, f y), (x + y, f (x + y)) are collinear. -/
lemma lemma_1 {f : ℝ → ℝ} (hf : ∀ x y, x * f x - y * f y = (x - y) * f (x + y)) (x y : ℝ) :
    Collinear ℝ {(x, f x), (y, f y), (x + y, f (x + y))} := by
  -- We first consider the case where x = 0, in which case the points are (0, f 0), (y, f y), (y, f y).
  -- There are only two distinct points, so the set is collinear.
  by_cases hx : x = 0
  . simp only [hx, zero_add, Set.mem_singleton_iff, Set.insert_eq_of_mem]
    exact collinear_pair _ _ _
  -- From here on, we assume x ≠ 0.
  specialize hf x y
  -- We now show that the points are collinear by showing that the vectors (x, f x), (-y, f (-y)), (y - x, f (y - x)) are affinely dependent.
  -- In the sense that a combination of them is zero and the weights sum to 0, but the weights are not all 0.
  rw [collinear_iff_not_affineIndependent_set, affineIndependent_def]
  push_neg
  -- We give the weights x; -y; y - x to the points (x, f x); (-y, f (-y)); (y - x, f (y - x)) respectively.
  -- We first show that the sum of the weights is 0.
  have h₁ : ∑ i ∈ Finset.univ, ![x, -y, y - x] i = 0 := by
    simp only [Finset.sum, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.univ_val_map, zero_add,
      List.ofFn_succ, Fin.isValue, Fin.cast_eq_self, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil,
      add_zero]
    ring
  refine ⟨Finset.univ, ![x, -y, y - x], h₁, ?_, 0, by simp [hx]⟩
  -- We now show that the linear combination is 0 by calculating it out.
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h₁ (0, 0)]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Prod.mk_zero_zero,
    Finset.weightedVSubOfPoint_apply, Finset.sum, vsub_eq_sub, sub_zero, Fin.univ_val_map,
    List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero, Prod.smul_mk, smul_eq_mul,
    Matrix.cons_val_succ, neg_smul, Prod.neg_mk, Matrix.cons_val_fin_one, List.ofFn_zero,
    Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero, Prod.mk_add_mk, Prod.mk_eq_zero]
  exact ⟨by ring, by linear_combination hf⟩

/- Lemma 2: If f satisfies the given functional equation, then the points (x, f x), (y, f y), (0， f 0) are collinear. -/
lemma lemma_2 {f : ℝ → ℝ} (hf : ∀ x y, x * f x - y * f y = (x - y) * f (x + y)) (x y : ℝ) (hx : x ≠ 0) : Collinear ℝ {(x, f x), (y, f y), (0, f 0)} := by
  -- By lemma 1, the points (x, f x), (y, f y), (x + y, f (x + y)) are collinear.
  have H₁ := lemma_1 hf x y
  -- By lemma 1, the points (x + y, f (x + y)), (-x, f (-x)), (y, f y) are collinear.
  have H₂ := lemma_1 hf (x + y) (-x)
  simp only [add_neg_cancel_comm] at H₂
  -- By lemma 1, the points (x, f x), (-x, f (-x)), (0, f 0) are collinear.
  have H₃ := lemma_1 hf x (-x)
  simp only [add_neg_cancel] at H₃
  -- We show that the points (x, f x), (-x, f (-x)) are distinct.
  -- Since x ≠ 0, we have x ≠ -x.
  have h₁ : (x, f x) ≠ (-x, f (-x)) := by
    simp only [ne_eq, Prod.mk.injEq, not_and_or]
    left
    contrapose! hx
    linarith only [hx]
  -- So (0, f 0) is on the line through (x, f x) and (-x, f (-x)).
  have H₄ : (0, f 0) ∈ affineSpan ℝ {(x, f x), (-x, f (-x))} := Collinear.mem_affineSpan_of_mem_of_ne H₃ (by simp) (by simp) (by simp) h₁
  -- We show that the points (y, f y), (x + y, f (x + y)) are distinct.
  -- Since x ≠ 0, we have x + y ≠ y.
  have h₂ : (y, f y) ≠ (x + y, f (x + y)) := by
    simp only [ne_eq, Prod.mk.injEq, not_and_or]
    exact Or.inl (self_ne_add_left.mpr hx)
  -- So (-x, f (-x)) is on the line through (y, f y) and (x + y, f (x + y)).
  have H₅ : (-x, f (-x)) ∈ affineSpan ℝ {(y, f y), (x + y, f (x + y))} := Collinear.mem_affineSpan_of_mem_of_ne H₂ (by simp) (by simp) (by simp) h₂
  -- So the line through (x, f x), (x + y, f (x + y)) is the same as the line through three points (x, f x), (y, f y), (x + y, f (x + y)).
  have H₆ : affineSpan ℝ {(y, f y), (x + y, f (x + y))} = affineSpan ℝ {(x, f x), (y, f y), (x + y, f (x + y))} := Collinear.affineSpan_eq_of_ne H₁ (by simp) (by simp) h₂
  rw [H₆] at H₅
  -- So the four points (-x, f (-x)), (x, f x), (y, f y), (x + y, f (x + y)) are collinear.
  rw [← collinear_insert_iff_of_mem_affineSpan H₅] at H₁
  -- So (y, f y) is on the line through (x, f x) and (-x, f (-x)).
  have H₇ : (y, f y) ∈ affineSpan ℝ {(x, f x), (-x, f (-x))} := Collinear.mem_affineSpan_of_mem_of_ne H₁ (by simp) (by simp) (by simp) h₁
  -- Therefore, we get (x, f x), (y, f y), (0, f 0) are collinear since they are all in the same line through (x, f x) and (-x, f (-x)).
  exact collinear_triple_of_mem_affineSpan_pair (p₄ := (x, f x)) (p₅ := (-x, f (-x))) (left_mem_affineSpan_pair _ _ _) H₇ H₄

/- $6 \cdot 179$ Find all functions $f: R \rightarrow R$, such that
$$
x f(x)-y f(y)=(x-y) f(x+y) .
$$ -/
theorem algebra_207476 : {f : ℝ → ℝ | ∀ x y, x * f x - y * f y = (x - y) * f (x + y)} = {fun x => a * x + b | (a : ℝ) (b : ℝ)} := by
  ext f
  constructor
  -- We first show that functions of the form a * x + b satisfy the functional equation.
  swap
  . rintro ⟨a, b, rfl⟩ x y
    ring
  -- We now show that any function that satisfies the functional equation must be of the form a * x + b.
  . simp only [Set.mem_setOf_eq]
    intro hf
    -- We set a := f 1 - f 0 and b := f 0.
    use f 1 - f 0, f 0
    ext x
    -- By lemma 2, the points (1, f 1), (x, f x), (0, f 0) are collinear.
    have H₁ := lemma_2 hf 1 x (by simp)
    -- So (x, f x) is on the line through (0, f 0) and (1, f 1).
    replace H₁ : (x, f x) ∈ affineSpan ℝ {(0, f 0), (1, f 1)} := Collinear.mem_affineSpan_of_mem_of_ne H₁ (by simp) (by simp) (by simp) (by simp)
    -- We express (x, f x) as (x, f x - f 0) +ᵥ (0, f 0).
    -- It is on the line through (0, f 0) and (1, f 1) if and only if the vector (x, f x - f 0) is a scalar multiple of the vector (1, f 1 - f 0).
    rw [show (x, f x) = (x, f x - f 0) +ᵥ ((0 : ℝ), f 0) by simp,
        vadd_left_mem_affineSpan_pair] at H₁
    -- So there exists a real number r such that (x, f x - f 0) = r * (1, f 1 - f 0).
    rcases H₁ with ⟨r, hr⟩
    -- After some simplification, we get r = x and f x - f 0 = r * (f 1 - f 0).
    simp only [vsub_eq_sub, Prod.mk_sub_mk, sub_zero, Prod.smul_mk, smul_eq_mul, mul_one,
      Prod.mk.injEq] at hr
    -- Now we are done.
    rcases hr with ⟨rfl, hr⟩
    linear_combination hr
