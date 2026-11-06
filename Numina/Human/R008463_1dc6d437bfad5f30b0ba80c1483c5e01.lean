import Mathlib

/- 5. (HUN 1) ${ }^{\mathrm{IMO}}$ Let $a, b, c, d, e$ be real numbers. Prove that the expression  $$ \begin{gathered} (a-b)(a-c)(a-d)(a-e)+(b-a)(b-c)(b-d)(b-e)+(c-a)(c-b)(c-d)(c-e) \\ +(d-a)(d-b)(d-c)(d-e)+(e-a)(e-b)(e-c)(e-d) \end{gathered} $$  is nonnegative. -/
theorem other_5808 (a b c d e : ℝ) :
  (a - b) * (a - c) * (a - d) * (a - e) +
  (b - a) * (b - c) * (b - d) * (b - e) +
  (c - a) * (c - b) * (c - d) * (c - e) +
  (d - a) * (d - b) * (d - c) * (d - e) +
  (e - a) * (e - b) * (e - c) * (e - d) ≥ 0 := by
  -- Without loss of generality, we may assume that a ≥ b ≥ c ≥ d ≥ e.
  wlog h : a ≥ b ∧ b ≥ c ∧ c ≥ d ∧ d ≥ e with H
  {
    clear h
    -- Rewrite the hypothesis using ∑ symbol.
    replace H (x : Fin 5 → ℝ) (hx : Monotone x) : ∑ i, ∏ j with j ≠ i, (x i - x j) ≥ 0 := by
      specialize H (x 4) (x 3) (x 2) (x 1) (x 0) ?_
      . refine ⟨?_, ?_, ?_, ?_⟩
        all_goals
          exact hx (by simp)
      simp [Finset.prod_filter]
      simp [Finset.sum, Finset.prod, Fin.succ]
      linarith only [H]
    -- Rewrite the goal using ∑ symbol.
    suffices K : ∀ x : Fin 5 → ℝ, ∑ i, ∏ j with j ≠ i, (x i - x j) ≥ 0 by
      specialize K ![a, b, c, d, e]
      simp [Finset.prod_filter] at K
      simp [Finset.sum, Finset.prod, Fin.succ] at K
      linarith only [K]
    -- Now we can sort the elements.
    intro x
    specialize H (x ∘ Tuple.sort x) (Tuple.monotone_sort x)
    -- It suffices to show that the sum is invariant under sorting.
    suffices ∑ i, ∏ j with j ≠ i, ((x ∘ Tuple.sort x) i - (x ∘ Tuple.sort x) j) = ∑ i, ∏ j with j ≠ i, (x i - x j) by
      linarith only [this, H]
    -- The product inside is invariant under sorting.
    have K (i : Fin 5) : ∏ j with j ≠ i, ((x ∘ Tuple.sort x) i - (x ∘ Tuple.sort x) j) = ∏ j with j ≠ Tuple.sort x i, (x (Tuple.sort x i) - x j) := by
      apply Finset.prod_bijective (Tuple.sort x) (Equiv.bijective _)
      . intro j
        simp
      . intro j hj
        simp at hj ⊢
    -- Now we can sum over the sorted elements.
    exact Fintype.sum_bijective (Tuple.sort x) (Equiv.bijective _) _ _ K
  }
  -- Simple lemma:
  -- If nonnegative numbers x y z x' y' z' satisfy x ≤ x', y ≤ y', z ≤ z'
  -- then x * y * z ≤ x' * y' * z'.
  have lem (x y z x' y' z' : ℝ) (hx : 0 ≤ x) (hx' : x ≤ x') (hy : 0 ≤ y) (hy' : y ≤ y') (hz : 0 ≤ z) (hz' : z ≤ z') : x * y * z ≤ x' * y' * z' := by
    -- Simple calculation.
    calc
      _ ≤ x * y * z' := mul_le_mul_of_nonneg_left hz' (mul_nonneg hx hy)
      _ = x * (y * z') := mul_assoc x y z'
      _ ≤ x * (y' * z') := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy' (le_trans hz hz')) hx
      _ ≤ x' * (y' * z') := mul_le_mul_of_nonneg_right hx' (mul_nonneg (le_trans hy hy') (le_trans hz hz'))
      _ = x' * y' * z' := (mul_assoc x' y' z').symm

  -- Now we can prove the original problem (with the ordering we assumed).
  -- Now (a - b) * (a - c) * (a - d) * (a - e) + (b - a) * (b - c) * (b - d) * (b - e) ≥ 0.
  have H₁ : (a - b) * (a - c) * (a - d) * (a - e) + (b - a) * (b - c) * (b - d) * (b - e) ≥ 0 := by
    calc
      _ = (a - b) * ((a - c) * (a - d) * (a - e) - (b - c) * (b - d) * (b - e)) := by ring
      _ ≥ 0 := mul_nonneg (by linarith) ?_
    rw [sub_nonneg]
    apply lem <;> linarith
  -- (d - e) * ((a - e) * (b - e) * (c - e) - (a - d) * (b - d) * (c - d)) ≥ 0.
  have H₂ : (d - a) * (d - b) * (d - c) * (d - e) + (e - a) * (e - b) * (e - c) * (e - d) ≥ 0 := by
    calc
      _ = (d - e) * ((a - e) * (b - e) * (c - e) - (a - d) * (b - d) * (c - d)) := by ring
      _ ≥ 0 := mul_nonneg (by linarith) ?_
    rw [sub_nonneg]
    apply lem <;> linarith
  -- (c - a) * (c - b) * (c - d) * (c - e) ≥ 0.
  have H₃ : (c - a) * (c - b) * (c - d) * (c - e) ≥ 0 := by
    have ⟨h₁, h₂, h₃, h₄⟩ : a - c ≥ 0 ∧ b - c ≥ 0 ∧ c - d ≥ 0 ∧ c - e ≥ 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        linarith
    calc
      _ = (a - c) * (b - c) * (c - d) * (c - e) := by ring
      _ ≥ 0 := by positivity
  -- Adding the three inequalities, we get the desired result.
  linarith only [H₁, H₂, H₃]
