import Mathlib

open Finset Complex

/- Lemma 1: If $z$ is a primitive 23-th root of unity, then
$$
\frac{1}{1+z+z^2} = 1 + \sum_{i=0}^{6} z^{3(i+1)}
$$ -/
lemma lemma_1 {z : ℂ} (hz : IsPrimitiveRoot z 23) :
    1 / (1 + z + z ^ 2) = 1 + ∑ i ∈ range 7, z ^ (3 * (i + 1)) := by
  -- We first show that $1 + z + z^2 \neq 0$.
  -- Since $z$ is a primitive 23-th root of unity, $z^3 \neq 1$.
  have h₁ := IsPrimitiveRoot.pow_ne_one_of_pos_of_lt hz (show 0 < 3 by simp) (by simp)
  -- Therefore, $1 + z + z^2 \neq 0$.
  replace h₁ : 1 + z + z ^ 2 ≠ 0 := by
    contrapose! h₁
    linear_combination h₁ * (z - 1)
  -- We now eliminate the denominator.
  field_simp [Finset.sum]
  -- Expand the sum.
  ring_nf
  -- RHS is $\sum_{i=0}^{23} z^i$.
  -- We have $\sum_{i=0}^{22} z^i = 0$ since $z$ is a primitive 23-th root of unity.
  have h₂ := IsPrimitiveRoot.geom_sum_eq_zero hz (by simp)
  simp [Finset.sum] at h₂
  have h₃ : z ^ 23 = 1 := hz.pow_eq_one
  -- The conclusion follows.
  linear_combination -h₂ - h₃

/- Lemma 2: If $z$ is a primitive 23-th root of unity, then $z^k$ is also a primitive 23-th root of unity, for any $0 < k < 23$. -/
lemma lemma_2 {z : ℂ} (hz : IsPrimitiveRoot z 23) {k : ℕ} (hk₁ : 0 < k) (hk₂ : k < 23) :
    IsPrimitiveRoot (z ^ k) 23 := IsPrimitiveRoot.pow_of_coprime hz k (Nat.coprime_of_lt_prime hk₁ hk₂ (by norm_num)).symm -- $k$ is coprime to $23$

/- Lemma 3: If $z$ is a primitive 23-th root of unity, then
$$
\frac{1}{1+z^{i+1}+z^{2(i+1)}} = 1 + \sum_{j=0}^{6} (z^{i+1})^{3(j+1)}
$$
for any $i \in \{0, 1, \ldots, 21\}$. -/
lemma lemma_3 {z : ℂ} (hz : IsPrimitiveRoot z 23) (i : ℕ) (hk : i ∈ range 22) :
    1 / (1 + z ^ (i + 1) + z ^ (2 * (i + 1))) = 1 + ∑ j ∈ range 7, (z ^ (i + 1)) ^ (3 * (j + 1)) := by
  -- $z^{i+1}$ is a primitive 23-th root of unity.
  have h₁ := lemma_2 hz (show 0 < i + 1 by simp) (by simp at hk ⊢; exact Nat.add_lt_of_lt_sub hk)
  -- Just apply lemma_1 and simplify.
  convert lemma_1 h₁ using 3
  exact pow_mul' z 2 (i + 1)

/- Lemma 4: If $z$ is a primitive 23-th root of unity, then
$$
\sum_{i=0}^{21} z^{i+1} = -1
$$ -/
lemma lemma_4 {z : ℂ} (hz : IsPrimitiveRoot z 23) :
    ∑ i ∈ range 22, z ^ (i + 1) = -1 := by
  -- Just apply the geometric sum formula.
  have h₁ := IsPrimitiveRoot.geom_sum_eq_zero hz (by simp)
  -- Delete the first term.
  rw [Finset.sum_range_succ', pow_zero] at h₁
  -- The conclusion follows.
  exact (neg_eq_of_add_eq_zero_left h₁).symm

/- Lemma 5: If $z$ is a primitive 23-th root of unity, then
$$
\sum_{x=0}^{21} (z^{x+1})^{3(y+1)} = -1
$$
for any $y \in \{0, 1, \ldots, 6\}$. -/
lemma lemma_5 {z : ℂ} (hz : IsPrimitiveRoot z 23) (y : ℕ) (hy : y ∈ range 7) :
    ∑ x ∈ range 22, (z ^ (x + 1)) ^ (3 * (y + 1)) = -1 := by
  -- Rewrite the power.
  rw [Finset.sum_congr rfl (fun x hx => pow_right_comm _ _ _)]
  -- Apply lemma_4.
  apply lemma_4
  -- We need to show that $z^{3(y+1)}$ is a primitive 23-th root of unity.
  simp at hy
  rw [pow_mul]
  -- Since $z^3$ is a primitive 23-th root of unity, $z^{3(y+1)}$ is a primitive 23-th root of unity by lemma_2.
  exact lemma_2 (IsPrimitiveRoot.pow_of_coprime hz 3 rfl) (by simp) (by omega)

/- Lemma 6: If $z$ is a non-real complex number with $z^{23}=1$, then $z$ is a primitive 23-th root of unity. -/
lemma lemma_6 {z : ℂ} (hz : z ^ 23 = 1) (hz' : z.im ≠ 0) : IsPrimitiveRoot z 23 := by
  -- It suffices to show that $z ^ l ≠ 1$ for all $0 < l < 23$.
  refine IsPrimitiveRoot.mk_of_lt z (by simp) hz (fun l hl₁ hl₂ => ?_)
  -- $l$ is coprime to $23$.
  have hl := Nat.coprime_of_lt_prime hl₁ hl₂ (by norm_num)
  -- Let's show that $z^l = 1$ implies $z$ is a real number.
  contrapose! hz'
  -- $z^gcd(l,23) = 1$.
  have h₁ := pow_gcd_eq_one z hz hz'
  -- That is, $z = 1$.
  rw [hl, pow_one] at h₁
  -- So $z$ is real.
  simp [h₁]

/- Let $z$ be a non-real complex number with $z^{23}=1$. Compute

$$
\sum_{k=0}^{22} \frac{1}{1+z^{k}+z^{2 k}}
$$ -/
theorem algebra_609078 (z : ℂ) (hz : z ^ 23 = 1) (hz' : z.im ≠ 0) :
    (∑ k ∈ range 23, (1 / (1 + z ^ k + z ^ (2 * k)))) = 46 / 3 := by
  -- $z$ is a primitive 23-th root of unity by lemma_6.
  replace hz := lemma_6 hz hz'
  -- Apply lemma_3, and switch the order of summation, and then apply lemma_5.
  rw [Finset.sum_range_succ', Finset.sum_congr rfl (lemma_3 hz), Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_congr rfl (lemma_5 hz)]
  -- Simplify.
  norm_num
