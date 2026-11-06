import Mathlib

open Finset Complex

/- 2. Given the complex number $z=\frac{-1+i \sqrt{3}}{2}$. Calculate the product:


$$

\left(z+\frac{1}{z}\right)\left(z^{2}+\frac{1}{z^{2}}\right) \ldots\left(z^{2012}+\frac{1}{z^{2012}}\right)

$$
 -/
theorem algebra_218940 {z : ℂ} (hz : z = (-1 + I * Real.sqrt 3) / 2) :
    ∏ i ∈ range 2012, (z^(i + 1) + 1 / z^(i + 1)) = 2^670 := by
  -- Comput z^2 = (-1 - √3 * I) / 2.
  have hz2 : z ^ 2 = (-1 - √3 * I) / 2 := by
    rw [hz]
    ring_nf
    rw [I_sq, show (√3 : ℂ) ^ 2 = (√3 ^ 2 : ℝ) by norm_cast]
    rw [Real.sq_sqrt zero_le_three]
    push_cast
    ring
  -- Compute z^3 = z^2 * z = 1.
  have hz3 : z ^ 3 = 1 := by
    rw [show 3 = 2 + 1 by norm_num, pow_add, hz2, pow_one, hz]
    ring_nf
    rw [I_sq, show (√3 : ℂ) ^ 2 = (√3 ^ 2 : ℝ) by norm_cast]
    rw [Real.sq_sqrt zero_le_three]
    norm_num
  -- We get 1 / z = z^2 (since z ^ 3 = 1).
  have hz_inv : 1 / z = z ^ 2 := by
    rw [div_eq_iff, ← pow_succ, hz3]
    simp [hz, ← normSq_pos, normSq]
    norm_num
  -- We get 1 / z^i = z^(2 * i).
  have hz_inv' i : 1 / z ^ i = z ^ (2 * i) := by
    rw [show (1 : ℂ) = 1 ^ i by simp, ← div_pow, hz_inv, pow_mul]
  -- z^3 = 1 implies that z^i = z^(i % 3).
  have hzi i : z ^ i = z ^ (i % 3) := by rw [pow_eq_pow_mod _ hz3]
  calc
    -- ∏ i ∈ range 2012, (z^(i + 1) + 1 / z^(i + 1))
    --    = (∏ i ∈ range 2010, (z^(i + 1) + 1 / z^(i + 1))) * (z^2 + z)^2
    -- (because z^2011 + 1 / z^2011 = z + z^2 and z^2012 + 1 / z^2012 = z^2 + z).
    _ = (∏ i ∈ range 2010, (z^(i + 1) + 1 / z^(i + 1))) * (z^2 + z)^2 := by
      rw [prod_range_succ, prod_range_succ, pow_two, ← mul_assoc]
      simp only [Nat.reduceAdd, hzi 2011, Nat.reduceMod, pow_one, hzi 2012, hz_inv, hz_inv', hzi 4]
      ring
    -- ∏ i ∈ range 2010, (z^(i + 1) + 1 / z^(i + 1))
    --    = ∏ k ∈ range 670, ∏ i ∈ [3 * k, 3 * k + 2], (z^(i + 1) + 1 / z^(i + 1)).
    _ = (∏ k ∈ range 670, ∏ i ∈ Icc (3 * k) (3 * k + 2), (z^(i + 1) + 1 / z^(i + 1))) * (z^2 + z)^2 := by
      congrm ?_ * _
      rw [← prod_biUnion]
      · apply prod_congr _ (fun _ _ => rfl)
        ext i
        simp only [mem_Icc, mem_biUnion, mem_range, mem_Ico]
        constructor
        · intro hi
          use i / 3
          omega
        · omega
      · simp only [Set.PairwiseDisjoint, Set.Pairwise, coe_range, Set.mem_Iio, ne_eq,
          Function.onFun, disjoint_iff_ne, mem_Icc, and_imp]
        omega
    -- ∏ i ∈ [3 * k, 3 * k + 2], (z^(i + 1) + 1 / z^(i + 1)) = (z^2 + z)^2 * 2.
    -- This result follows from z^(3 * i + r) = z^r and z^3 + 1 / z^3 = 2.
    _ = (∏ k ∈ range 670, (z^2 + z)^2 * (1 + 1)) * (z^2 + z)^2 := by
      congrm ?_ * _
      apply prod_congr rfl
      intro i hi
      repeat rw [prod_Icc_succ_top (by omega)]
      rw [Icc_self, prod_singleton]
      have eq1 : z^(3 * i + 1) = z := by
        rw [hzi, Nat.mul_add_mod]
        norm_num
      have eq2 : z^(3 * i + 1 + 1) = z^2 := by
        rw [hzi, show 3 * i + 1 + 1 = 3 * i + 2 by ring, Nat.mul_add_mod]
      have eq3 : z^(3 * i + 1 + 1 + 1) = 1 := by
        rw [hzi, show 3 * i + 1 + 1 + 1 = 3 * (i + 1) by ring, Nat.mul_mod]
        norm_num
      rw [eq1, eq2, eq3, hz_inv, hz_inv', hzi 4]
      ring
    -- We get (z^2 + z)^(2 * 670 + 2) * 2^670.
    _ = (z^2 + z)^(2 * 670 + 2) * 2^670 := by
      simp only [prod_const, card_range, mul_pow, ← pow_mul]
      generalize 670 = n
      ring
    -- z^2 + z = -1 and (z^2 + z)^(2 * 670 + 2) = (-1)^1342.
    _ = (-1)^1342 * 2^670 := by
      rw [show 2 * 670 + 2 = 1342 by norm_num]
      congrm ?_ ^ _ * _
      rw [hz2, hz]
      ring
    -- (-1)^1342 = 1.
    _ = 2^670 := by rw [Even.neg_one_pow (by decide), one_mul]