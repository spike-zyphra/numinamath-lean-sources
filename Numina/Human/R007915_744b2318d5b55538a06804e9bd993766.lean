import Mathlib

/-
PROBLEM: The graph of the polynomial $P(x) = x^5 + a x^4 + b x^3 + c x^2 + d x + e$ has five distinct $x$-intercepts,
one of which is at $(0,0)$. Which of the following coefficients cannot be zero?
-/
theorem AMC_Algebra_96191 (a b c d e : ℝ) (h : ∃ x1 x2 x3 x4 x5 : ℝ, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x1 ≠ x5 ∧
x2 ≠ x3 ∧ x2 ≠ x4 ∧ x2 ≠ x5 ∧ x3 ≠ x4 ∧ x3 ≠ x5 ∧ x4 ≠ x5 ∧
(x1^5 + a * x1^4 + b * x1^3 + c * x1^2 + d * x1 + e = 0 ∧
x2^5 + a * x2^4 + b * x2^3 + c * x2^2 + d * x2 + e = 0 ∧
x3^5 + a * x3^4 + b * x3^3 + c * x3^2 + d * x3 + e = 0 ∧
x4^5 + a * x4^4 + b * x4^3 + c * x4^2 + d * x4 + e = 0 ∧
x5^5 + a * x5^4 + b * x5^3 + c * x5^2 + d * x5 + e = 0 ∧
x1 = 0)) :
d ≠ 0 := by
  rcases h with ⟨r₁, r₂, r₃, r₄, r₅, hr12, hr13, hr14, hr15, hr23, hr24, hr25, hr34, hr35, hr45, hr1eq, hr2eq, hr3eq, hr4eq, hr5eq, hr1eq0⟩
  -- $P(x) = x^5 + a x^4 + b x^3 + c x^2 + d x + e$
  let P:Polynomial ℝ := Polynomial.X ^5 + Polynomial.C a * Polynomial.X^4 + Polynomial.C b * Polynomial.X^3 + Polynomial.C c * Polynomial.X^2 + Polynomial.C d * Polynomial.X^1 + Polynomial.C e

  -- $r_1, r_2, r_3, r_4, r_5$ are roots of $P(x)$
  have hr_Root: P.IsRoot r₁ ∧ P.IsRoot r₂ ∧ P.IsRoot r₃ ∧ P.IsRoot r₄ ∧ P.IsRoot r₅:= by
    dsimp only [Polynomial.IsRoot, P]
    simp only [pow_one, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C]
    exact ⟨hr1eq, hr2eq, hr3eq, hr4eq, hr5eq⟩

  -- The degree of $P(x)$ is 5
  have hP_degree: P.natDegree =  5 := by
      apply P.natDegree_eq_of_le_of_coeff_ne_zero
      · dsimp only [P]
        calc
        (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4 + Polynomial.C b * Polynomial.X ^ 3 + Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d * Polynomial.X^1 + Polynomial.C e).natDegree ≤ (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4 + Polynomial.C b * Polynomial.X ^ 3 + Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d * Polynomial.X^1).natDegree ⊔  (Polynomial.C e).natDegree := by
          apply Polynomial.natDegree_add_le (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4 + Polynomial.C b * Polynomial.X ^ 3 + Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d * Polynomial.X^1) (Polynomial.C e)

        _ ≤ (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4 + Polynomial.C b * Polynomial.X ^ 3 + Polynomial.C c * Polynomial.X ^ 2).natDegree ⊔  (Polynomial.C d * Polynomial.X^1).natDegree ⊔  (Polynomial.C e).natDegree := by
          apply sup_le_sup_right
          apply Polynomial.natDegree_add_le (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4 + Polynomial.C b * Polynomial.X ^ 3 + Polynomial.C c * Polynomial.X ^ 2) (Polynomial.C d * Polynomial.X^1)

        _ ≤ (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4 + Polynomial.C b * Polynomial.X ^ 3).natDegree ⊔ (Polynomial.C c * Polynomial.X ^ 2).natDegree ⊔  (Polynomial.C d * Polynomial.X^1).natDegree ⊔  (Polynomial.C e).natDegree := by
          repeat apply sup_le_sup_right
          apply Polynomial.natDegree_add_le  (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4 + Polynomial.C b * Polynomial.X ^ 3) (Polynomial.C c * Polynomial.X ^ 2)
        _ ≤ (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4).natDegree ⊔  (Polynomial.C b * Polynomial.X ^ 3).natDegree ⊔ (Polynomial.C c * Polynomial.X ^ 2).natDegree ⊔  (Polynomial.C d * Polynomial.X^1).natDegree ⊔  (Polynomial.C e).natDegree := by
          repeat apply sup_le_sup_right
          apply Polynomial.natDegree_add_le  (Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 4) (Polynomial.C b * Polynomial.X ^ 3)
        _ ≤ (Polynomial.X ^ 5).natDegree ⊔  (Polynomial.C a * Polynomial.X ^ 4).natDegree ⊔  (Polynomial.C b * Polynomial.X ^ 3).natDegree ⊔ (Polynomial.C c * Polynomial.X ^ 2).natDegree ⊔  (Polynomial.C d * Polynomial.X^1).natDegree ⊔  (Polynomial.C e).natDegree := by
          repeat apply sup_le_sup_right
          apply Polynomial.natDegree_add_le (Polynomial.X ^ 5) (Polynomial.C a * Polynomial.X ^ 4)
        _ ≤ 5 := by
          simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one,
            Polynomial.natDegree_C, le_sup_iff, zero_le, or_self, sup_of_le_left, sup_le_iff,
            le_refl, true_and]
          constructor
          · constructor
            · constructor
              · constructor
                · exact  Polynomial.natDegree_C_mul_X_pow_le a 4
              · apply le_trans (Polynomial.natDegree_C_mul_X_pow_le b 3)
                simp
            · apply le_trans (Polynomial.natDegree_C_mul_X_pow_le c 2)
              simp
          · apply le_trans (Polynomial.natDegree_C_mul_X_pow_le d 1)
            simp

      · dsimp only [P]
        simp


  have hP_ne_zero : P ≠ 0 := by
    intro h
    have h1: P.coeff 5 = 0 := by
      rw [h]
      exact rfl
    have h2: P.coeff 5 = 1 := by
      dsimp only [P]
      simp
    rw [h1] at h2
    simp at h2

  -- The roots of $P(x)$ are $r₁, r₂, r₃, r₄, r₅$
  have hP_roots: P.roots = {r₁, r₂, r₃, r₄, r₅} := by
    apply Eq.symm
    apply Multiset.eq_of_le_of_card_le
    · have: ({r₁, r₂, r₃, r₄, r₅}:Multiset ℝ).Nodup := by
        simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
          Multiset.mem_singleton, not_or, Multiset.nodup_singleton, and_true]
        exact ⟨⟨hr12, hr13, hr14, hr15⟩, ⟨hr23, hr24, hr25⟩, ⟨hr34, hr35⟩, hr45⟩


      apply (Multiset.le_iff_subset this).mpr
      simp only [Multiset.insert_eq_cons, Multiset.cons_subset, Polynomial.mem_roots', ne_eq, Multiset.singleton_subset]
      exact ⟨⟨hP_ne_zero, hr_Root.1⟩, ⟨hP_ne_zero, hr_Root.2.1⟩, ⟨hP_ne_zero, hr_Root.2.2.1⟩, ⟨hP_ne_zero, hr_Root.2.2.2.1⟩, ⟨hP_ne_zero, hr_Root.2.2.2.2⟩⟩
    · simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton, Nat.reduceAdd]
      rw [← hP_degree]
      apply Polynomial.card_roots'


  -- $d = r₁ * r₂ * r₃ * r₄ + r₁ * r₂ * r₃ * r₅ + r₁ * r₂ * r₄ * r₅ + r₁ * r₃ * r₄ * r₅ + r₂ * r₃ * r₄ * r₅$
  have hd: d = r₁ * r₂ * r₃ * r₄ + r₁ * r₂ * r₃ * r₅ + r₁ * r₂ * r₄ * r₅ + r₁ * r₃ * r₄ * r₅ + r₂ * r₃ * r₄ * r₅ := by
    have: P.coeff 1 = d := by
      dsimp only [P]
      simp
    rw [← this]

    -- The leading coefficient of $P(x)$ is 1
    have: P.leadingCoeff = 1 := by
      dsimp only [Polynomial.leadingCoeff,]
      rw [hP_degree]
      dsimp only [P]
      simp

    rw [P.coeff_eq_esymm_roots_of_card]
    · rw [this, hP_degree, hP_roots]
      dsimp only [Multiset.esymm]
      simp only [Nat.add_one_sub_one, one_mul, Multiset.insert_eq_cons, Multiset.powersetCard_cons,
        Nat.reduceAdd, Multiset.card_cons, Multiset.card_singleton, Nat.lt_add_one,
        Multiset.powersetCard_eq_empty, Nat.one_lt_ofNat, zero_add, Multiset.map_map,
        Function.comp_apply, Multiset.powersetCard_zero_left, Multiset.map_singleton,
        Multiset.cons_zero, Multiset.map_add, Multiset.prod_cons, Multiset.prod_singleton,
        Multiset.sum_add, Multiset.sum_singleton]
      have: Multiset.powersetCard 1 {r₅} = {{r₅}} := by exact rfl
      rw [this]
      simp only [Multiset.map_singleton, Multiset.prod_singleton, Multiset.sum_singleton]
      linarith

    · rw [hP_roots, hP_degree]
      simp
    · rw [hP_degree]
      simp

  rw [hr1eq0] at hr12
  rw [hr1eq0] at hr13
  rw [hr1eq0] at hr14
  rw [hr1eq0] at hr15
  rw [hr1eq0] at hd
  simp only [zero_mul, add_zero, zero_add] at hd
  rw [hd]
  apply mul_ne_zero_iff.mpr
  constructor
  · apply mul_ne_zero_iff.mpr
    · constructor
      · apply mul_ne_zero_iff.mpr
        constructor
        · exact id (Ne.symm hr12)
        · exact id (Ne.symm hr13)
      · exact id (Ne.symm hr14)
  · exact id (Ne.symm hr15)