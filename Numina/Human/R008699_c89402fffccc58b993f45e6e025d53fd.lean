import Mathlib

open Finset

/-
Problem Statement:
  Let $n \geqslant 2$ be a positive integer and $a_{1}, a_{2}, \ldots, a_{n}$ be real numbers such that
  \[ a_{1}+a_{2}+\cdots+a_{n}=0 \]
  Define the set $A$ by
  \[ A=\left\{(i, j)\left|1 \leqslant i < j \leqslant n,\left|a_{i}-a_{j}\right| \geqslant 1\right\} .\right. \]
  Prove that, if $A$ is not empty, then
  \[ \sum_{(i, j) \in A} a_{i} a_{j}<0 \]
  (China)
Solution:
  Define sets $B$ and $C$ by  $$ \begin{aligned} & B=\left\{(i, j)\left|1 \leqslant i, j \leqslant n,\left|a_{i}-a_{j}\right| \geqslant 1\right\},\right. \\ & C=\left\{(i, j)\left|1 \leqslant i, j \leqslant n,\left|a_{i}-a_{j}\right|<1\right\} .\right. \end{aligned} $$  We have  $$ \begin{aligned} \sum_{(i, j) \in A} a_{i} a_{j} & =\frac{1}{2} \sum_{(i, j) \in B} a_{i} a_{j} \\ \sum_{(i, j) \in B} a_{i} a_{j} & =\sum_{1 \leqslant i, j \leqslant n} a_{i} a_{j}-\sum_{(i, j) \notin B} a_{i} a_{j}=0-\sum_{(i, j) \in C} a_{i} a_{j} . \end{aligned} $$  So it suffices to show that if $A$ (and hence $B$ ) are nonempty, then  $$ \sum_{(i, j) \in C} a_{i} a_{j}>0 $$  Partition the indices into sets $P, Q, R$, and $S$ such that  $$ \begin{aligned} P & =\left\{i \mid a_{i} \leqslant-1\right\} & R & =\left\{i \mid 0 < a_{i}<1\right\} \\ Q & =\left\{i \mid-1 < a_{i} \leqslant 0\right\} & S & =\left\{i \mid 1 \leqslant a_{i}\right\} . \end{aligned} $$  Then  $$ \sum_{(i, j) \in C} a_{i} a_{j} \geqslant \sum_{i \in P \cup S} a_{i}^{2}+\sum_{i, j \in Q \cup R} a_{i} a_{j}=\sum_{i \in P \cup S} a_{i}^{2}+\left(\sum_{i \in Q \cup R} a_{i}\right)^{2} \geqslant 0 . $$  The first inequality holds because all of the positive terms in the RHS are also in the LHS, and all of the negative terms in the LHS are also in the RHS. The first inequality attains equality only if both sides have the same negative terms, which implies $\left|a_{i}-a_{j}\right|<1$ whenever $i, j \in Q \cup R$; the second inequality attains equality only if $P=S=\varnothing$. But then we would have $A=\varnothing$. So $A$ nonempty implies that the inequality holds strictly, as required.
-/
theorem algebra_23702 {n : ℕ} (a : Fin n → ℝ) (hsum : ∑ i : Fin n, a i = 0) :
    -- Use `let` to simplify the expression, because the set `A` occurs twice.
    let A := univ.filter (fun (i, j) => i < j ∧ |a i - a j| ≥ 1)
    A.Nonempty → ∑ ⟨i, j⟩ ∈ A, a i * a j < 0 := by
  intro A ne
  -- Define a new set `C`, which will be used in the following proof.
  let C := univ.filter (fun (i, j) => |a i - a j| < 1)
  -- Establish the fact that if the sum over `C` is positive, then the sum over `A` is negative.
  suffices ∑ ⟨i, j⟩ ∈ C, a i * a j > 0 by
    -- Define `A'`, which is the image of `A` under the symmetry (i, j) ↦ (j, i).
    let A' := univ.filter (fun (i, j) => j < i ∧ |a i - a j| ≥ 1)
    -- Define the set `B`, it is the union of `A` and `A'`, so the sum over `B` is
    -- twice of the sum over `A`.
    let B := univ.filter (fun (i, j) => |a i - a j| ≥ 1)
    have B_eq_2A : ∑ ⟨i, j⟩ ∈ B, a i * a j = 2 * ∑ ⟨i, j⟩ ∈ A, a i * a j := calc
      -- The sum over `B` can be splitted into sums over `A` and `A'`.
      _ = ∑ ⟨i, j⟩ ∈ A, a i * a j + ∑ ⟨i, j⟩ ∈ A', a i * a j := by
        -- Firstly, we prove that `B` is the union of `A` and `A'`.
        have : B = A ∪ A' := by
          ext x
          simp only [B, ge_iff_le, mem_filter, mem_univ,
            true_and, A, A', mem_union]
          -- We only need to prove this lemma, and the remaining is a tautology.
          have : 1 ≤ |a x.1 - a x.2| → x.1 < x.2 ∨ x.1 > x.2 := by
            simp only [gt_iff_lt, lt_or_lt_iff_ne, ne_eq]
            intro h eq
            rw [eq] at h
            absurd h
            simp
          -- Use `tauto` to solve a propositional tautology.
          tauto
        -- Split the sum over `B` using the disjointness of `A` and `A'`.
        rw [this]
        apply sum_union
        -- Use `ext` and `simp [A, A']` to convert the goal of disjointness to a goal
        -- that `x` can't be both elements of `A` and `A'`.
        rw [disjoint_iff_inter_eq_empty]
        ext x
        simpa [A, A'] using fun lt _ gt => (Fin.lt_asymm lt gt).elim
      _ = _ := by
        -- Prove that the sum over `A` and `A'` are equal by swapping the indices in `A'`.
        rw [sum_bijective (e := Prod.swap) (t := A') (g := fun (i, j) => a i * a j)]
        · linarith
        · apply Prod.swap_bijective
        · simp [A, A', abs_sub_comm]
        · simp [mul_comm]
    -- Prove that the sum of the summation over `C` and the summation over `B` is zero.
    have C_add_B : ∑ ⟨i, j⟩ ∈ C, a i * a j + ∑ ⟨i, j⟩ ∈ B, a i * a j = 0 := calc
      _ = ∑ ⟨i, j⟩ : Fin n × Fin n, a i * a j := by
        rw [show univ = C ∪ B by ext; simp [B, C]; by_contra h; simp at h; linarith]
        refine (sum_union ?_).symm
        rw [disjoint_iff_inter_eq_empty]
        ext x
        simp [B, C]
      -- Using `univ_product_univ` to expand the sum, and simplify it to zero using
      -- the assumption `hsum`, which states that the summation of all `a` is zero.
      _ = (∑ i : Fin n, a i) * ∑ i : Fin n, a i := by
        rw [← univ_product_univ, sum_product]
        exact Fintype.sum_mul_sum a a |>.symm
      _ = 0 := by simp [hsum]
    -- With `B = 2A` and `C + B = 0`, we can prove the main result `A < 0` assuming `C > 0`.
    linarith
  -- Define `P` as the indices where `|a i| ≥ 1`. It is `P ∪ S` in the solution text.
  let P := univ.filter (fun i => |a i| ≥ 1)
  -- Define `Q` as the indices where `|a i| < 1`. It is `Q ∪ R` in the solution text.
  let Q := univ.filter (fun i => |a i| < 1)
  -- Define `R` as a certain subset of the complement of `C`.
  let R := (Q ×ˢ Q).filter (fun (i, j) => |a i - a j| ≥ 1)
  -- Start a calculation to lower-bound the sum over `C`.
  calc
    -- The sum over `C` is at least the sum over `diag(P) ∪ (Q × Q) \ R`, where `diag` means
    -- the diagonal over some one-dimensional set.
    _ ≥ ∑ ⟨i, j⟩ ∈ P.image (fun i => (i, i)) ∪ (Q ×ˢ Q \ R), a i * a j := by
      apply sum_le_sum_of_subset_of_nonneg
      · -- Show that every element of `diag(P) ∪ (Q × Q) \ R` is belonging to `C`.
        intro ⟨i, j⟩ hij
        simp [C, R] at hij ⊢
        cases' hij with hij hij
        · simp [hij.2]
        · exact hij.2 hij.1.1 hij.1.2
      · -- Show that the summands are non-negative on the complement of
        -- `diag(P) ∪ (Q × Q) \ R` in `C`. This is a tedious proof. Firstly, we use `simp`
        -- to expand the notations such as `C`, `Q` and `R`.
        simp [C, Q, R]
        rintro i j h - hQ
        -- If `|a i| < 1` and `|a j| < 1`, then `(i, j) ∈ R`, which contradicts.
        have hij : |a i| ≥ 1 ∨ |a j| ≥ 1 := by
          by_contra h
          simp only [ge_iff_le, not_or, not_le] at h
          specialize hQ h.1 h.2
          linarith
        clear hQ
        -- We need only to consider the case of `|a i| ≥ 1`, because indices `i` and `j` are symmetric
        -- in all hypotheses and the goal.
        wlog hi : |a i| ≥ 1 generalizing i j
        · cases' hij with hij hij
          · exact this i j h (.inl hij) hij
          · rw [mul_comm]
            exact this j i (by simpa [abs_sub_comm]) (.inl hij) hij
        · clear hij
          -- We split into two cases. If `a i ≥ 0`, we can prove `a j ≥ 0`; if `a i ≤ 0`, we can
          -- also prove that `a j ≤ 0`, so in both cases we have `a i * a j ≥ 0`.
          by_cases hi' : a i ≥ 0
          · -- `a i ≥ 1` and the distance of `a i` and `a j` is less than `1`, so `a j` is positive.
            rw [abs_of_nonneg hi'] at hi
            apply mul_nonneg hi'
            calc
              -- Proving using inequalities of the absolute value and `linarith`.
              _ ≥ a i - |a i - a j| := by
                have : a i - a j ≤ |a i - a j| := by apply le_abs_self
                linarith
              _ ≥ _ := by linarith
          · -- This case is similar to the first case. We have `a i ≤ -1` and `|a i - a j| < 1`,
            -- so `a j ≤ a i + |a i - a j| < 0`.
            simp only [ge_iff_le, not_le] at hi'
            rw [abs_of_nonpos (by linarith)] at hi
            apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
            calc
              _ ≤ a i + |a i - a j| := by
                have : a i - a j ≥ -|a i - a j| := by apply neg_abs_le
                linarith
              _ ≤ _ := by linarith
    -- The union set in the summation range can be splitted, and it's a disjoint union.
    _ = ∑ i ∈ P, a i ^ 2 + ∑ ⟨i, j⟩ ∈ Q ×ˢ Q \ R, a i * a j := by
      rw [sum_union]
      · congr 1
        simp [pow_two]
      · rw [disjoint_iff_inter_eq_empty]
        ext ⟨i, j⟩
        simpa [P, Q, R] using fun le _ i_lt j_lt => ⟨i_lt, j_lt, by linarith⟩
    -- Rewriting the sum on `Q × Q \ R` to the substraction of the sum on `Q × Q` minus
    -- the sum on `R`. We add brackets to use the `congr` tactic.
    _ = ∑ i ∈ P, a i ^ 2 + ((∑ i ∈ Q, a i) ^ 2 - ∑ ⟨i, j⟩ ∈ R, a i * a j) := by
      congr 1
      simp only [pow_two, sum_mul_sum, eq_sub_iff_add_eq,
        ← sum_product (f := fun (i, j) => a i * a j)]
      apply sum_sdiff
      simp [R]
    -- Remove the second summand `(∑ i ∈ Q, a i) ^ 2`.
    _ ≥ ∑ i ∈ P, a i ^ 2 + ∑ ⟨i, j⟩ ∈ R, -a i * a j := by
      simp
      nlinarith   -- Use `nlinarith` tactic to deal with the `(...) ^ 2` term.
    -- Prove that the final expression is strictly positive.
    _ > 0 := by
      have h₁ : ∀ i ∈ P, 0 < a i ^ 2 := by
        intro i hi
        simp only [P, ge_iff_le, mem_filter, mem_univ, true_and] at hi
        rw [← sq_abs]
        nlinarith
      -- Prove that the terms in `R` contribute positively due to their definitions.
      have h₂ : ∀ x ∈ R, 0 < -a x.1 * a x.2 := by
        intro ⟨i, j⟩ hij
        simp [Q, R] at hij
        simp only [neg_mul, Left.neg_pos_iff]
        -- Use some algebraic tricks to prove the inequality. With these methods,
        -- we can avoid tedious case-splitting of positivity of `a i` and `a j`.
        -- Firstly, because `|a i| < 1` and `|a j| < 1`, we have `a i * a j < 2`.
        have : a i * a j - 2 < 0 := by
          simp only [sub_neg]
          calc
            _ ≤ |a i| * |a j| := by rw [← abs_mul]; apply le_abs_self
            _ < 1 := by
              apply Left.mul_lt_of_lt_of_le_one_of_nonneg hij.1.1 (le_of_lt hij.1.2) (by simp)
            _ < 2 := by simp
        refine neg_of_mul_pos_left ?_ (le_of_lt this)
        -- So we only need to prove that `0 < a i * a j * (a i * a j - 2)`.
        calc
          _ = 0 + 0 := by simp
          -- Obviously the following term is positive.
          _ < (a i ^ 2 - 1) * (a j ^ 2 - 1) + ((a i - a j) ^ 2 - 1) := by
            apply add_lt_add_of_lt_of_le
            apply mul_pos_of_neg_of_neg
            · simpa using hij.1.1
            · simpa using hij.1.2
            · simpa using hij.2
          -- An algebra trick: the previous positive term is just equal to `a i * a j * (a i * a j - 2)`.
          _ = _ := by ring
      -- Prove that either set `P` or `R` is nonempty, guaranteeing positivity of the sum.
      have P_or_R : P.Nonempty ∨ R.Nonempty := by
        by_contra h
        -- If both `P` and `R` are empty, `A` would be zero, which contradicts the assumption
        -- in this problem.
        simp [P, Q, R, eq_empty_iff_forall_not_mem] at h
        rcases h with ⟨h, h'⟩
        simp [A, nonempty_iff_ne_empty, eq_empty_iff_forall_not_mem] at ne
        obtain ⟨i, j, _, hij⟩ := ne
        have := h' i j (h i) (h j)
        linarith
      -- If `P` is nonempty, the first summand is positive and the second summand
      -- is non-negative. If `R` is non-empty, it's similar.
      rcases P_or_R with P_ne | R_ne
      · exact add_pos_of_pos_of_nonneg (sum_pos h₁ P_ne)
          (sum_nonneg (fun _ hx => le_of_lt (h₂ _ hx)))
      · exact add_pos_of_nonneg_of_pos (sum_nonneg (fun _ hx => le_of_lt (h₁ _ hx)))
          (sum_pos h₂ R_ne)
