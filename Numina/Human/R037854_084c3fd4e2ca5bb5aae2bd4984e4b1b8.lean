import Mathlib

/- How many integers are there in the solution set of $|x-2| \leq 5.6$? -/
theorem algebra_10476: Set.ncard {x:ℤ | |x-2| ≤ (5.6:ℝ)} = 11 := by
  have lemma_cast_le(x y:ℤ): x ≤ y ↔ (x:ℝ) ≤ y := by
    exact Iff.symm Int.cast_le
  have h56: 5 ≤ (5.6:ℝ) := by norm_num
  have h56': -5.6 ≤ (-5:ℝ) := by norm_num
  -- x is integer, so we claim |x-2| ≤ 5.6 is equivalent to |x-2|≤ 5.
  have h1: {x:ℤ | |x-2| ≤ (5.6:ℝ)} = {x:ℤ | |x-2| ≤ 5} := by
    ext x; simp; constructor <;> intro h
    <;> rw [abs_le] at h <;> rw [abs_le]
    -- in this direction, we argue |x-2| ≤ 5.6 leads to |x-2| ≤ 5.
    -- since x is integer. if not, then we have |x-2| > 5, which leads to |x-2| ≥ 6. contradiction.
    · have ht1: -5 ≤ x-2 := by
        by_contra! hc
        have tt1: x-2 ≤ -5-1 := Int.le_sub_one_of_lt hc
        rw [lemma_cast_le (x-2) (-5-1)] at tt1
        simp at tt1
        have tt2 := h.left; simp at tt2
        have tt3: 6+x ≤ x+(5.6:ℝ) := le_trans tt1 tt2
        have tt4: (5.6:ℝ) < 6 := by norm_num
        rw [add_comm] at tt3
        have ntt3: x+(5.6:ℝ) < x+6 := by
          exact (Real.add_lt_add_iff_left ↑x).mpr tt4
        linarith [tt3,ntt3]
      have ht2: x-2 ≤ 5 := by
        by_contra! hc
        have hc1: 5 ≤ x-2-1 := by
          exact Int.le_sub_one_of_lt hc
        have tt1: x ≥ (8:ℝ) := by
          suffices (8:ℝ) ≤ x by
            exact this
          apply (lemma_cast_le 8 x).mp
          linarith [hc1]
        have tt2: x ≤ (7.6:ℝ) := by
          have hh1 := h.right
          have hh2: (7.6:ℝ) = 5.6+2 := by norm_num
          rw [hh2]
          linarith [hh1]
        have tt3: (7.6:ℝ) ≥ 8 := ge_trans tt2 tt1
        norm_num at tt3
      exact ⟨ht1,ht2⟩
    rw [lemma_cast_le, lemma_cast_le] at h; simp at h
    -- this direction is easy. |x-2| ≤ 5, then |x-2| ≤ 5.6
    constructor
    · linarith [h.left, h56']
    · linarith [h.right, h56]
  -- solve |x-2| ≤ 5, we have -3 ≤ x ≤ 7
  have h2: {x:ℤ| |x-2| ≤ 5} = {x:ℤ | x ≥ -3 ∧ x ≤ 7} := by
    ext x; simp; rw [abs_le]
    constructor <;> intro h
    <;> exact ⟨(by linarith [h.left]), (by linarith [h.right])⟩
  -- for integer x satisfy -3 ≤ x ≤ 7, x = -3,-2,-1,0,1,2,3,4,5,6,7.
  have h3: {x:ℤ | x ≥ -3 ∧ x ≤ 7} = {-3,-2,-1,0,1,2,3,4,5,6,7} := by
    ext x; simp; constructor <;> intro h
    · have hx1 := h.left
      have hx2 := h.right
      interval_cases x
      all_goals simp
    · rcases h with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
      all_goals simp [ht]
  rw [h1, h2, h3]
  -- obviously, -3,-2,...,7 have 11 elements in total.
  let f: (i:ℕ) → i < 11 → ℤ := fun i h => i-3
  have f_def: f = (fun (i:ℕ) (h: i<11) => ((i:ℤ)-3)) := rfl
  apply Set.ncard_eq_of_bijective f
  · intro a; simp; intro h
    use (a+3).toNat
    have ht1: 0 ≤ a+3 := by
      omega
    have ht2: (a+3).toNat < 11 := by
      have tt1: (a+3).toNat = a+3 := by
        exact Int.toNat_of_nonneg ht1
      have tt2: a+3 < 11 := by
        omega
      rw [← tt1] at tt2
      exact Int.ofNat_lt.mp tt2
    use ht2
    rw [f_def]; simp [ht1]
  · intro i h
    rw [f_def]; simp
    have ht1: (i:ℤ)-3 < 8 := by
      have: (i:ℤ) < 11 := by
        exact Int.lt_toNat.mp h
      linarith [this]
    have ht2: (i:ℤ)-3 ≤ 7 := by
      exact Int.lt_add_one_iff.mp ht1
    have ht3: 0 ≤ (i:ℤ) := by
      exact Int.ofNat_zero_le i
    interval_cases i; all_goals simp
  · intro i j hi hj heq
    rw [f_def] at heq; simp at heq; apply heq