import Mathlib

/- Compute the sum $S=\sum_{i=0}^{101} \frac{x_{i}^{3}}{1-3 x_{i}+3 x_{i}^{2}}$ for $x_{i}=\frac{i}{101}$.
Answer: $S=51$.-/
theorem algebra_604724 {x : ℕ → ℝ} (hx : ∀ i, x i = i / 101) :
    ∑ i ∈ Finset.range 102, x i ^ 3 / (1 - 3 * x i + 3 * x i ^ 2) = 51 := by
  -- Since $x_{101-i}=\frac{101-i}{101}=1-\frac{i}{101}=1-x_{i}$ and
  have key1 {i : ℕ} (hi : i ∈ Finset.range 102) : x (101 - i) = 1 - x i := by
    simp at hi
    simp [hx]
    rw [Nat.cast_sub (by omega)]
    ring
  -- $$ 1-3 x_{i}+3 x_{i}^{2}=\left(1-3 x_{i}+3 x_{i}^{2}-x_{i}^{3}\right)+x_{i}^{3}=
  -- \left(1-x_{i}\right)^{3}+x_{i}^{3}=x_{101-i}^{3}+x_{i}^{3}, $$
  have key2 {i : ℕ} (hi : i ∈ Finset.range 102) : 1 - 3 * x i + 3 * x i ^ 2 =
      x (101 - i) ^ 3 + x i ^ 3 := by
    rw [key1 hi]
    ring
  -- We need this lemma to perform `field_simp`,
  have key3 {i : ℕ} (hi : i ∈ Finset.range 102) : x (101 - i) ^ 3 + x i ^ 3 ≠ 0 := by
    rw [key1 hi]
    intro h
    replace h : (1 - x i) ^ 3 = (-x i) ^ 3 := by linear_combination h
    have : StrictMono (fun y : ℝ => y ^ 3) := Odd.strictMono_pow (by norm_num [Nat.odd_iff])
    have := this.injective
    have := this h
    norm_num at this
  -- Suffices to show `2S=102`.
  rw [← mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0)]
  -- We change `∑ i, xi^3/(1-3xi+3xi^2)` to `∑ i, xi^3/(x(101-i)^3+xi^3)`.
  calc 2 * ∑ i ∈ Finset.range 102, x i ^ 3 / (1 - 3 * x i + 3 * x i ^ 2)
    _ = 2 * ∑ i ∈ Finset.range 102, x i ^ 3 / (x (101 - i) ^ 3 + x i ^ 3) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      exact key2 hi
  rw [two_mul, eq_comm]
  -- Notice that `∑ i, (xi^3 + x(101-i)^3) / (xi^3 + x(101-i)^3)` equals to `102`.
  calc 2 * 51
    _ = ∑ _ ∈ Finset.range 102, (1 : ℝ) := by simpa using by norm_num
    _ = ∑ i ∈ Finset.range 102, (x (101 - i) ^ 3 + x i ^ 3) / (x (101 - i) ^ 3 + x i ^ 3) := by
      apply Finset.sum_congr rfl
      intro i hi
      have := key3 hi
      field_simp
  conv_lhs => rhs; intro i; rw [add_div]
  rw [Finset.sum_add_distrib, add_comm]
  -- Now we need to show that `∑ i, x(101-i)^3/(xi^3 + x(101-i)^3)` equals to `∑ i, xi^3/(xi^3 + x(101-i)^3)`.
  congr 1
  -- This is obvious by using the reflection of `Finst.sum`.
  rw [eq_comm, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 102 - 1 - i = 101 - i by omega]
  congr 1
  rw [add_comm]
  congr
  simp at hi
  omega
