import Mathlib


/- Let $a_{1}, a_{2}, \ldots, a_{9}$ be any non-negative numbers such that $a_{1}=a_{9}=0$ and at least one of the numbers is non-zero.
Prove that for some $i, 2 \leq i \leq 8$, the inequality $a_{i-1}+a_{i+1}<2 a_{i}$ holds.
Will the statement remain true if we change the number 2 in the last inequality to $1.9 ?$ -/
theorem inequalities_606371 (a : Fin 9 → ℝ)
    (h₀ : ∀ i, 0 ≤ a i)
    (h₁ : a 0 = 0)
    (h₂ : a 8 = 0)
    (h₃ : ∃ i, a i ≠ 0) :
    (∃ i, 1 ≤ i ∧ i ≤ 7 ∧ a (i - 1) + a (i + 1) < 2 * a i) ∧
    (∃ i, 1 ≤ i ∧ i ≤ 7 ∧ a (i - 1) + a (i+1) < 1.9 * a i) := by

  -- we prove a more general result.
  have {r:ℝ} (rpos: 0 < r)
    (r2pos: 0 < r - 1/r)
    (r3pos: 0 < r - 1 / (r - 1/r))
    (r4pos: 0 < r - 1 / (r - 1 / (r - 1/r)))
    (r5pos: 0 < r - 1 / (r - 1 / (r - 1 / (r - 1/r))))
    (r6pos: 0 < r - 1 / (r - 1 / (r - 1 / (r - 1 / (r - 1/r)))))
    (r7pos: 0 < r - 1 / (r - 1 / (r - 1 / (r - 1 / (r - 1 / (r - 1/r)))))):
    ∃ i, 1 ≤ i ∧ i ≤ 7 ∧ a (i-1) + a (i+1) < r * a i := by
    -- suppose on the contrary, it does not hold for any i.
    by_contra! h

    -- r x ≤ y, then y ≥ 1/r x
    have div_r {rr x y: ℝ} (rrpos: 0 < rr) (h: rr * x ≤ y):
      1/rr * y ≥ x := by
      simp only [one_div, ge_iff_le]
      exact (le_inv_mul_iff₀' rrpos).mpr h

    -- ra1 ≤ a0 + a2
    have h1: r * a 1 ≤ a 2 := by
      specialize h 1 le_rfl (by simp)
      simp only [h₁, Fin.isValue, sub_self, Fin.reduceAdd, zero_add] at h
      exact h

    -- ra2 ≤ a1 + a3
    have h2: r * a 2 ≤ a 1 + a 3 := by
      specialize h 2 (by simp) (by simp)
      simp only [Fin.isValue, Fin.reduceSub, Fin.reduceAdd] at h
      exact h
    -- from h1, express a1 in terms of a2

    set r2 := r - 1/r with r2_def
    -- when r = 1.9, r2 is about 1.37
    replace h2: r2 * a 2 ≤ a 3 := by
      rw [r2_def, sub_mul]
      replace h1: 1/r * a 2 ≥ a 1 := div_r rpos h1
      linarith only [h1, h2]

    -- ra3 ≤ a2 + a4
    have h3: r * a 3 ≤ a 2 + a 4 := by
      specialize h 3 (by simp) (by simp)
      simp only [Fin.isValue, Fin.reduceSub, Fin.reduceAdd] at h
      exact h
    set r3 := r - 1/r2 with r3_def
    -- when r = 1.9, r3 is about 1.17
    replace h3: r3 * a 3 ≤ a 4 := by
      rw [r3_def, sub_mul]
      replace h2 := div_r r2pos h2
      linarith only [h2, h3]

    -- ra4 ≤ a3 + a5
    have h4: r * a 4 ≤ a 3 + a 5 := by
      specialize h 4 (by simp) (by simp)
      simp only [Fin.isValue, Fin.reduceSub, Fin.reduceAdd] at h
      exact h
    set r4 := r - 1/r3 with r4_def
    -- when r = 1.9, r4 is about 1.045
    replace h4: r4 * a 4 ≤ a 5 := by
      rw [r4_def, sub_mul]
      replace h3 := div_r r3pos h3
      linarith only [h3, h4]

    -- ra5 ≤ a4 + a6
    have h5: r * a 5 ≤ a 4 + a 6 := by
      specialize h 5 (by simp) (by simp)
      simp only [Fin.isValue, Fin.reduceSub, Fin.reduceAdd] at h
      exact h
    set r5 := r - 1/r4 with r5_def
    -- when r = 1.9, r5 is about 0.943
    replace h5: r5 * a 5 ≤ a 6 := by
      rw [r5_def, sub_mul]
      replace h4 := div_r r4pos h4
      linarith only [h4, h5]

    -- ra6 ≤ a5 + a7
    have h6: r * a 6 ≤ a 5 + a 7 := by
      specialize h 6 (by simp) (by simp)
      simp only [Fin.isValue, Fin.reduceSub, Fin.reduceAdd] at h
      exact h
    set r6 := r - 1/r5 with r6_def
    -- when r = 1.9, r6 is about 0.84
    replace h6: r6 * a 6 ≤ a 7 := by
      rw [r6_def, sub_mul]
      replace h5 := div_r r5pos h5
      linarith only [h5, h6]

    -- ra7 ≤ a6 + a8
    have h7: r * a 7 ≤ a 6 + a 8 := by
      specialize h 7 (by simp) le_rfl
      simp at h
      exact h
    set r7 := r - 1/r6 with r7_def
    -- when r = 1.9, r7 is about 0.7
    replace h7: r7 * a 7 ≤ a 8 := by
      rw [r7_def, sub_mul]
      replace h6 := div_r r6pos h6
      linarith only [h6, h7]

    -- so a1 to a8 are all zero.
    have eqzero_of {rr x:ℝ} (rrpos: 0 < rr)
      (npos: rr * x ≤ 0) (nneg: 0 ≤ x): x = 0 := by
      apply le_antisymm ?_ nneg
      exact nonpos_of_mul_nonpos_right npos rrpos


    replace h7 : a 7 = 0 := by
      rw [h₂] at h7
      apply eqzero_of r7pos h7
      apply h₀
    replace h6: a 6 = 0 := by
      rw [h7] at h6
      apply eqzero_of r6pos h6
      apply h₀
    replace h5: a 5 = 0 := by
      rw [h6] at h5
      apply eqzero_of r5pos h5
      apply h₀
    replace h4: a 4 = 0 := by
      rw [h5] at h4
      apply eqzero_of r4pos h4
      apply h₀
    replace h3: a 3 = 0 := by
      rw [h4] at h3
      apply eqzero_of r3pos h3
      apply h₀
    replace h2: a 2 = 0 := by
      rw [h3] at h2
      apply eqzero_of r2pos h2
      apply h₀
    replace h1: a 1 = 0 := by
      rw [h2] at h1
      apply eqzero_of rpos h1
      apply h₀

    -- then h₃ is false
    clear * - h₃ h7 h6 h5 h4 h3 h2 h1 h₂ h₁
    rcases h₃ with ⟨i, ainz⟩
    have: i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by
      clear * -
      decide +revert
    rcases this with (hi | hi | hi | hi | hi | hi | hi | hi | hi)
    all_goals
      rw [hi] at ainz
      contradiction

  -- substitute r = 2,  r = 1.9, done.
  constructor <;> apply this
  all_goals norm_num