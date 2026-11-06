import Mathlib

open Real Finset

/- 1. (5 points) Find the degree measure of the angle


$$

\delta=\arccos \left(\left(\sin 2541^{\circ}+\sin 2542^{\circ}+\cdots+\sin 6141^{\circ}\right)^{\cos } 2520^{\circ}+\cos 2521^{\circ}+\cdots+\cos 6120^{\circ}\right)

$$
 -/
theorem algebra_196013 :
    arccos ((∑ i : ℕ in Icc 2541 6141, sin (i * π / 180)) ^ (∑ i ∈ Icc (2520 : ℕ) 6120, cos (i * π / 180))) = 69 * π / 180 := by
  -- Prove that ∑ i ∈ range (360 : ℕ), sin (x + i * π / 180) = 0 for any x
  have sum_sin360 x : ∑ i ∈ range (360 : ℕ), sin (x + i * π / 180) = 0 := calc
    -- Split the sum into two sums: over [0, 180) and over [180, 360)
    ∑ i ∈ range (360 : ℕ), sin (x + i * π / 180) = ∑ i ∈ range 180, sin (x + i * π / 180) + ∑ i ∈ Ico (180 : ℕ) 360, sin (x + i * π / 180) := by
        have hs : range 360 = range 180 ∪ Ico 180 360 := by
          rw [range_eq_Ico, Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]
        have hs_disj : Disjoint (range 180) (Ico 180 360) := by
          rw [range_eq_Ico]
          exact Ico_disjoint_Ico_consecutive 0 180 360
        rw [hs, sum_union hs_disj]
    -- ∑ i ∈ [180, 360), sin (i * π / 180) = ∑ i ∈ [0, 180), sin ((x + i * π / 180) + π)
    _ = ∑ i ∈ range 180, sin (x + i * π / 180) + ∑ i ∈ range 180, sin ((x + i * π / 180) + π) := by
        congrm _ + ?_
        rw [sum_Ico_eq_sum_range]
        apply sum_congr rfl
        intro i hi
        simp [show x + (180 + i) * π / 180 = (x + i * π / 180) + π by ring]
    -- sin ((x + i * π / 180) + π) = -sin (x + i * π / 180)
    -- and so the total sum is 0
    _ = ∑ i ∈ range 180, sin (x + i * π / 180) - ∑ i ∈ range 180, sin (x + i * π / 180) := by
        simp only [sin_add_pi, sum_neg_distrib, add_neg_cancel, sub_self]
    _ = 0 := by rw [sub_eq_zero]
  -- Show that for any natural a b (b > 0) we have
  -- ∑ i ∈ [a, a + b * 360], sin (i * π / 180) = sin ((a + b * 360) * π / 180)
  have sum_sin (a b : ℕ) (hb : 0 < b): ∑ i ∈ Icc a (a + b * 360), sin (i * π / 180) = sin ((a + b * 360) * π / 180) := calc
    -- Rewrite the sum over [a, a + b * 360) as the sum for j ∈ [0, b) of sums for i ∈ [a + j * 360, a + (j + 1) * 360)
    ∑ i ∈ Icc a (a + b * 360), sin (i * π / 180) = ∑ j ∈ range b, ∑ i ∈ Ico (a + j * 360) (a + (j + 1) * 360), sin (i * π / 180) + sin ((a + b * 360) * π / 180) := by
        rw [show a + b * 360 = (a + b * 360 - 1) + 1 by omega]
        rw [sum_Icc_succ_top (by omega)]
        congr 1 <;> [skip; (congr; norm_cast; omega)]
        -- We need to show that [a, a + b * 360) = ⋃ j ∈ [0, b), [a + j * 360, a + (j + 1) * 360) and
        -- the sets [a + j * 360, a + (j + 1) * 360) are pairwise disjoint.
        rw [←Finset.sum_biUnion]
        · apply sum_congr _ (fun _ _ => rfl)
          ext i
          simp only [mem_Icc, mem_biUnion, mem_range, mem_Ico]
          constructor
          · intro h
            use (i - a) / 360
            omega
          · omega
        · simp only [Set.PairwiseDisjoint, Set.Pairwise, coe_range, Set.mem_Iio, ne_eq,
            Function.onFun, disjoint_iff_ne, mem_Ico, and_imp]
          omega
    -- ∑ i ∈ [a + j * 360, a + (j + 1) * 360), sin (i * π / 180)
    --   = ∑ i ∈ [0, 360), sin ((a + 360 * j) * π / 180 + i * π / 180)
    _ = ∑ j ∈ range b, ∑ i ∈ range 360, sin ((a + 360 * j) * π / 180 + i * π / 180) + sin ((a + b * 360) * π / 180) := by
        congrm ∑ j ∈ range b, ?_ + _
        rw [sum_Ico_eq_sum_range]
        apply sum_congr (by congr 1; omega)
        intro i hi
        congr 1
        push_cast
        ring
    -- We proved that ∑ i ∈ [0, 360), sin ((a + 360 * j) * π / 180 + i * π / 180) = 0
    -- for all a and j.
    _ = ∑ j ∈ range b, 0 + sin ((a + b * 360) * π / 180) := by
        congrm ?_ + _
        apply sum_congr rfl
        intro i hi
        rw [sum_sin360]
    -- The total sum is equal to the last term: sin ((a + b * 360) * π / 180)
    _ = sin ((a + b * 360) * π / 180) := by simp only [sum_const_zero, zero_add]
  -- Compute the sum ∑ i ∈ [2541, 6141], sin (i * π / 180).
  -- We have 6141 = 2541 + 10 * 360 so we can apply sum_sin with a = 2541 and b = 10
  -- and get ∑ i ∈ [2541, 6141], sin (i * π / 180)
  --                  = sin (6141 * π / 180)
  --                  = sin ((π / 2 - 69 * π / 180) + 17 * (2 * π))
  --                  = cos (69 * π / 180).
  have eq1 : ∑ i ∈ Icc (2541 : ℕ) 6141, sin (i * π / 180) = cos (69 * π / 180) := by
    rw [sum_sin 2541 10 (by norm_num)]
    norm_num
    rw [show 6141 * π / 180 = (π / 2 - 69 * π / 180) + (17 : ℤ) * (2 * π) by push_cast; ring]
    rw [sin_add_int_mul_two_pi, sin_pi_div_two_sub]
  -- Compute the sum ∑ i ∈ [2520, 6120], cos (i * π / 180).
  have eq2 : ∑ i ∈ Icc (2520 : ℕ) 6120, cos (i * π / 180) = 1 := calc
    -- We obtain ∑ i ∈ [2520, 6120], cos (i * π / 180) = -∑ i ∈ [2430 + 90, 6030 + 90], sin (i * π / 180)
    -- from cos ((90 + i) * π / 180) = -sin (i * π / 180).
    ∑ i ∈ Icc (2520 : ℕ) 6120, cos (i * π / 180) = -∑ i ∈ Icc (2430 : ℕ) 6030, sin (i * π / 180) := by
        rw [show Icc (2520 : ℕ) 6120 = Ico (2430 + 90) (6031 + 90) from rfl]
        rw [← sum_Ico_add, ← sum_neg_distrib]
        apply sum_congr rfl
        intro i hi
        push_cast
        rw [show (90 + i) * π / 180 = i * π / 180 + π / 2 by ring]
        rw [cos_add_pi_div_two]
    -- Now we can apply sum_sin with a = 2430 and b = 10 and get
    -- -∑ i ∈ [2430, 6030], sin (i * π / 180) = -sin (6030 * π / 180).
    _ = -sin (6030 * π / 180) := by
        rw [sum_sin 2430 10 (by norm_num)]
        norm_num
    -- We have sin (6030 * π / 180) = sin (π / 2 + 16 * (2 * π) + π) = -1.
    _ = 1 := by
        rw [show 6030 * π / 180 = π / 2 + (16 : ℤ) * (2 * π) + π by push_cast; ring]
        rw [sin_add_pi]
        rw [sin_add_int_mul_two_pi, sin_pi_div_two, neg_neg]
  -- Rewrite the original goal and get
  -- arccos (cos (69 * π / 180) ^ 1) = 69 * π / 180.
  rw [eq1, eq2, rpow_one, arccos_cos (by positivity) (by linarith [pi_pos])]