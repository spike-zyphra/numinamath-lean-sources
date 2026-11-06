import Mathlib

/- For how many integers $n$ is it true that $\sqrt{n} \le \sqrt{4n - 6} < \sqrt{2n + 5}$? -/
theorem algebra_10240 : {n : ℤ | (n : ℝ) ≥ 0 ∧ (4*n-6 : ℝ) ≥ 0 ∧ (2*n+5 : ℝ) ≥ 0 ∧ √n ≤ √(4*n-6) ∧ √(4*n-6) < √(2*n+5)}.ncard = 4 := by

  -- The solution set of the inequalities is {x : ℝ | 2 ≤ x ∧ x < 11/2}
  have H (x : ℝ) (hx1 : x ≥ 0) (hx2 : 4*x-6 ≥ 0) (hx3 : 2*x+5 ≥ 0) : (√x ≤ √(4*x-6) ∧ √(4*x-6) < √(2*x+5)) ↔ (2 ≤ x ∧ x < 11/2) := by
    -- Square both sides of the inequalities
    rw [Real.sqrt_le_sqrt_iff hx2, Real.sqrt_lt_sqrt_iff hx2]
    -- Only linear arithmetic is needed
    constructor
    all_goals
      intro h
      constructor <;> linarith only [h]

  -- Apply the previous result
  -- This lemma is pure tautology and I would not like to comment on it
  have K : {n : ℤ | (n : ℝ) ≥ 0 ∧ (4*n-6 : ℝ) ≥ 0 ∧ (2*n+5 : ℝ) ≥ 0 ∧ √n ≤ √(4*n-6) ∧ √(4*n-6) < √(2*n+5)} = {n : ℤ | 2 ≤ (n : ℝ) ∧ (n : ℝ) < 11/2} := by
    ext n
    constructor
    . intro ⟨h1, h2, h3, h⟩
      exact (H n h1 h2 h3).1 h
    . intro h
      simp at h
      have ⟨h1, h2, h3⟩ : (n : ℝ) ≥ 0 ∧ (4*n-6 : ℝ) ≥ 0 ∧ (2*n+5 : ℝ) ≥ 0 := by
        refine ⟨?_, ?_, ?_⟩
        all_goals
          linarith
      refine ⟨h1, h2, h3, ?_⟩
      exact (H n h1 h2 h3).2 h

  -- The set is now {n : ℤ | 2 ≤ ↑n < 11/2}
  rw [K]
  -- It is the preimage of the set {x : ℝ | 2 ≤ x < 11/2} under the cast function
  change (Int.cast ⁻¹' (Set.Ico (2 : ℝ) (11 / 2))).ncard = 4
  -- Which is equal to Set.Ico ⌊2⌋ ⌈11 / 2⌉
  rw [Int.preimage_Ico]

  -- Rewrite the ceiling to a floor to use norm_num
  rw [show 11 / 2 = - (- 11 / 2 : ℝ) by norm_num,
      Int.ceil_neg]
  norm_num

  -- Final simplification
  rw [← Finset.coe_Ico, Set.ncard_coe_Finset]
  simp
