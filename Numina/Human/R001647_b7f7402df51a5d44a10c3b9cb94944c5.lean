import Mathlib

open Matrix

/- Changing signs of all numbers in one row does not change the absolute value of the determinant. -/
lemma abs_det_eq_of_neg_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : |det (A.updateRow i ((-1 : ℝ) • (fun j => A i j)))| = |det A| := by
  rw [det_updateRow_smul, updateRow_eq_self]
  simp

/- Changing signs of all numbers in one colomn does not change the absolute value of the determinant. -/
lemma abs_det_eq_of_neg_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : |det (A.updateCol i ((-1 : ℝ) • (fun j => A j i)))| = |det A| := by
  rw [det_updateCol_smul, updateCol_eq_self]
  simp

/- Exchanging two rows or two columns does not change the absolute value of the determinant. -/
lemma abs_det_eq_of_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {σ₁ σ₂ : Fin n ≃ Fin n} : |det (A.reindex σ₁ σ₂)| = |det A| := by
  trans |det (A.submatrix σ₁ σ₂)|
  · simp
  · rw [abs_det_submatrix_equiv_equiv]

/- Performing any of the four operations does not change the absolute value of the determinant. -/
lemma abs_det_eq_of_op
    {op : Set (Matrix (Fin 5) (Fin 5) ℝ) → Set (Matrix (Fin 5) (Fin 5) ℝ)}
    (hop : op = fun S => {Y | ∃ X ∈ S,
        (∃ i, Y = X.updateRow i ((-1 : ℝ) • (fun j => X i j))) ∨
        (∃ i, Y = X.updateCol i ((-1 : ℝ) • (fun j => X j i))) ∨
        (∃ i j, Y = X.reindex (Equiv.swap i j) 1) ∨
        (∃ i j, Y = X.reindex 1 (Equiv.swap i j))})
    (S : Set (Matrix (Fin 5) (Fin 5) ℝ)) :
    ∀ Y ∈ op S, ∃ X ∈ S, |Y.det| = |X.det| := by
  intro Y hY
  rw [hop] at hY
  obtain ⟨X, hX, h⟩ := hY
  use X, hX
  -- We have four cases, depending on which operation was used.
  rcases h with h | h | h | h
  · -- 1. Changing signs of all numbers in one row.
    obtain ⟨i, hY⟩ := h
    rw [hY]
    exact abs_det_eq_of_neg_row X i
  · -- 2. Changing signs of all numbers in one column.
    obtain ⟨i, hY⟩ := h
    rw [hY]
    exact abs_det_eq_of_neg_col X i
  · -- 3. Exchanging two rows.
    obtain ⟨i, j, hY⟩ := h
    rw [hY]
    exact abs_det_eq_of_perm X
  · -- 4. Exchanging two columns.
    obtain ⟨i, j, hY⟩ := h
    rw [hY]
    exact abs_det_eq_of_perm X

/- Performing any times of these operations does not change the absolute value of the determinant. -/
lemma abs_det_eq_of_n_iterated_op
    {op : Set (Matrix (Fin 5) (Fin 5) ℝ) → Set (Matrix (Fin 5) (Fin 5) ℝ)}
    (hop : op = fun S => {Y | ∃ X ∈ S,
        (∃ i, Y = X.updateRow i ((-1 : ℝ) • (fun j => X i j))) ∨
        (∃ i, Y = X.updateCol i ((-1 : ℝ) • (fun j => X j i))) ∨
        (∃ i j, Y = X.reindex (Equiv.swap i j) 1) ∨
        (∃ i j, Y = X.reindex 1 (Equiv.swap i j))})
    {S : Set (Matrix (Fin 5) (Fin 5) ℝ)} {n : ℕ} :
    ∀ Y ∈ op^[n] S, ∃ X ∈ S, |Y.det| = |X.det| := by
  -- We prove this by induction on n.
  induction n generalizing S with
  | zero =>
    -- If n = 0, then Y is in S.
    intro Y hY
    simp at hY
    use Y
  | succ n ih =>
    -- If n > 0, apply the induction hypothesis to Y.
    -- There exists Z in op(S) such that |Y.det| = |Z.det|.
    intro Y hY
    simp at hY
    apply ih at hY
    obtain ⟨Z, hZ ,h⟩ := hY
    -- By the lemma abs_det_eq_of_op, there exists X in S such that |Z.det| = |X.det|.
    obtain ⟨X, hX, hdet⟩ := abs_det_eq_of_op hop S Z hZ
    use X, hX
    rw [h, hdet]

/- If the rows of A is not linear-independent, then det A = 0 -/
lemma det_eq_zero_of_not_linearIndependent {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ¬ LinearIndependent ℝ (fun i ↦ A i)) :
    det A = 0 := by
  obtain ⟨c, hc0, i, hci⟩ := Fintype.not_linearIndependent_iff.1 hA
  have h0 := A.det_updateRow_sum i c
  rwa [det_eq_zero_of_row_eq_zero (i := i) (fun j ↦ by simp [hc0]), smul_eq_mul, eq_comm,
    mul_eq_zero_iff_left hci] at h0

/- 12. (SWE 6) Consider the two square matrices
$$ A=\left[\begin{array}{rrrrr} 1 & 1 & 1 & 1 & 1 \\ 1 & 1 & 1 & -1 & -1 \\ 1 & -1 & -1 & 1 & 1
\\ 1 & -1 & -1 & -1 & 1 \\ 1 & 1 & -1 & 1 & -1 \end{array}\right] \quad \text { and }
\quad B=\left[\begin{array}{rrrrr} 1 & 1 & 1 & 1 & 1 \\ 1 & 1 & 1 & -1 & -1 \\
1 & 1 & -1 & 1 & -1 \\ 1 & -1 & -1 & 1 & 1 \\ 1 & -1 & 1 & -1 & 1 \end{array}\right] $$  with entries 1 and -1 .
The following operations will be called elementary: (1) Changing signs of all numbers in one row;
(2) Changing signs of all numbers in one column; (3) Interchanging two rows (two rows exchange their positions);
 (4) Interchanging two columns.  Prove that the matrix $B$ cannot be obtained from the matrix $A$ using these operations. -/
theorem algebra_24967 {A B : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : A = !![1, 1, 1, 1, 1; 1, 1, 1, -1, -1; 1, -1, -1, 1, 1; 1, -1, -1, -1, 1; 1, 1, -1, 1, -1])
    (hB : B = !![1, 1, 1, 1, 1; 1, 1, 1, -1, -1; 1, 1, -1, 1, -1; 1, -1, -1, 1, 1; 1, -1, 1, -1, 1])
    {op : Set (Matrix (Fin 5) (Fin 5) ℝ) → Set (Matrix (Fin 5) (Fin 5) ℝ)}
    (hop : op = fun S => {Y | ∃ X ∈ S,
        (∃ i, Y = X.updateRow i ((-1 : ℝ) • (fun j => X i j))) ∨
        (∃ i, Y = X.updateCol i ((-1 : ℝ) • (fun j => X j i))) ∨
        (∃ i j, Y = X.reindex (Equiv.swap i j) 1) ∨
        (∃ i j, Y = X.reindex 1 (Equiv.swap i j))}) :
    ¬ ∃ n, B ∈ op^[n] {A} := by

  -- We first compute the determinants of A.
  -- A.det = 16
  have hA : A.det = 16 := by
    rw [hA]
    -- Directly expanding the determinant of A.
    simp only [det_succ_row_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, of_apply, cons_val',
      empty_val', cons_val_fin_one, cons_val_zero, submatrix_apply, Fin.succ_zero_eq_one, cons_val_one, head_cons,
      submatrix_submatrix, Function.comp_apply, Fin.succ_one_eq_two, cons_val_two, tail_cons, cons_val_succ, det_unique,
      Fin.default_eq_zero, head_fin_const, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, Fin.zero_succAbove,
      Finset.univ_unique, Fin.val_succ, Fin.val_eq_zero, zero_add, pow_one, neg_mul, Fin.succ_succAbove_zero,
      Finset.sum_neg_distrib, Finset.sum_singleton, Fin.succ_succAbove_one, even_two, Even.neg_pow, one_pow,
      Fin.succAbove_succ_self, mul_one, mul_neg, neg_neg, add_neg_cancel, mul_zero, neg_add_rev, neg_add_cancel, add_zero,
      Fin.succ_succAbove_succ, Fin.one_succAbove_succ, Fin.succAbove, Fin.castSucc, Fin.castAdd, Fin.castLE]
    simp [Fin.lt_iff_val_lt_val]
    have : @Fin.val 5 3 = 3 := by
      exact rfl
    simp [this]
    norm_num

  -- B.det = 0
  have hB : B.det = 0 := by
    -- As for B, we can use the fact that the rows of B are not linear-independent to simplify the calculation.
    apply det_eq_zero_of_not_linearIndependent
    apply not_linearIndependent_iff.mpr
    -- Note that B * (0, 1, -1, 1, -1) = 0,
    -- so the rows of B are not linear-independent.
    let x : Fin 5 → ℝ := ![0, 1, -1, 1, -1]
    use Finset.univ, x
    constructor
    · simp [x, hB, Fin.sum_univ_five]
      ext i
      fin_cases i
      all_goals
        simp
    · use 1
      simp [x]

  -- Now we prove that B cannot be obtained from A using the operations defined by op.
  -- We will prove this by contradiction.
  by_contra h
  -- Assume that there exists n such that B ∈ op^[n] {A}.
  -- By the lemma abs_det_eq_of_n_iterated_op, there exists X in {A} such that |B.det| = |X.det|.
  -- Since {A} is a singleton set, we have X = A.
  obtain ⟨n, hmem⟩ := h
  apply abs_det_eq_of_n_iterated_op hop at hmem
  simp at hmem
  -- We have |B.det| = |A.det|, which means |0| = |16|.
  -- This is a contradiction.
  simp [hA, hB] at hmem
