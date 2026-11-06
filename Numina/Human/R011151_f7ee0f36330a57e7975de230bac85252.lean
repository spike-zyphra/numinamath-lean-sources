import Mathlib

/- Lemma 1: a(x + 1) ^ (1/a) ≤ x + a -/
lemma lemma_1 {x : ℝ} (hx : 0 < x) (a : ℕ) (ha : 0 < a) :
    a * (x + 1) ^ ((1 : ℝ) / a) ≤ x + a := by
  -- By Bernoulli's inequality
  -- We have (1 + x) ^ (1/a) ≤ 1 + 1/a*x
  have H := rpow_one_add_le_one_add_mul_self (show -1 ≤ x by linarith) (show 0 ≤ (1 : ℝ) / a by simp) (show (1 : ℝ) / a ≤ 1 from div_le_one_of_le₀ (Nat.one_le_cast.mpr ha) (by simp))
  -- We multiply both sides by a and simplify
  calc a * (x + 1) ^ ((1 : ℝ) / a)
    _ = a * ((1 + x) ^ ((1 : ℝ) / a)) := by ring_nf
    _ ≤ a * (1 + 1 / a * x) := (mul_le_mul_iff_of_pos_left (by simp [ha])).mpr H
    _ = x + a := by field_simp; ring

/- Lemma 2: a(x + 1) ^ (1/a) < x + a if a > 1.
It is a strict version of Lemma 1. -/
lemma lemma_2 {x : ℝ} (hx : 0 < x) (a : ℕ) (ha : 1 < a) :
    a * (x + 1) ^ ((1 : ℝ) / a) < x + a := by
  -- By Bernoulli's inequality(strict version)
  -- We have (1 + x) ^ (1/a) < 1 + 1/a*x
  have H := rpow_one_add_lt_one_add_mul_self (show -1 ≤ x by linarith) (show x ≠ 0 from hx.ne') (show 0 < (1 : ℝ) / a by positivity) (show (1 : ℝ) / a < 1 from (div_lt_one (by positivity)).mpr (by simp [ha]))
  -- We multiply both sides by a and simplify
  calc a * (x + 1) ^ ((1 : ℝ) / a)
    _ = a * ((1 + x) ^ ((1 : ℝ) / a)) := by ring_nf
    _ < a * (1 + 1 / a * x) := (mul_lt_mul_iff_of_pos_left (by positivity)).mpr H
    _ = x + a := by field_simp; ring

/- Let $a_{1}, \ldots, a_{n}, k, M$ be strictly positive integers such that $\sum_{i=1}^{n} \frac{1}{a_{i}}=k$ and $\prod_{i=1}^{n} a_{i}=M$. If $M>1$, show that the polynomial $P(x)=M(x+1)^{k}-\left(x+a_{1}\right) \ldots\left(x+a_{n}\right)$ has no strictly positive root. -/
theorem algebra_109097 {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (k M : ℕ) (hk : 0 < k) (hM : 1 < M)
    (hsum : ∑ i, (1 : ℝ) / a i = k) (hprod : ∏ i, a i = M) :
    ¬∃ x : ℝ, 0 < x ∧ M * (x + 1) ^ k - ∏ i, (x + a i) = 0 := by
  -- We prove that for any x > 0, M * (x + 1) ^ k < ∏ i, (x + a i)
  push_neg
  intro x hx
  refine ne_of_lt (sub_lt_zero.mpr ?_)
  -- We rewrite M * (x + 1) ^ k = ∏ i, (a i * (x + 1) ^ (1/a i)) by algebraic manipulation
  calc M * (x + 1) ^ k
    _ = (∏ i, (a i : ℝ)) * (x + 1) ^ (k : ℝ) := by rify at hprod; simp [hprod]
    _ = (∏ i, (a i : ℝ)) * (x + 1) ^ (∑ i, (1 : ℝ) / a i) := by rw [hsum]
    _ = (∏ i, (a i : ℝ)) * ∏ i, (x + 1) ^ ((1 : ℝ) / a i) := by rw [Real.rpow_sum_of_pos (by positivity)]
    _ = ∏ i, (a i * (x + 1) ^ ((1 : ℝ) / a i)) := by rw [Finset.prod_mul_distrib]
    _ < ∏ i, (x + a i) := by
      -- To prove strict inequality between two products, it suffices to prove non-strict inequality for each term, and to find a term in which the inequality is strict.
      apply Finset.prod_lt_prod
      . rintro i -
        specialize ha i
        positivity
      . rintro i -
        exact lemma_1 hx (a i) (ha i)
      . -- To find a term in which the inequality is strict, we only need to find one i such that a i > 1 thanks to Lemma 2.
        rsuffices ⟨i, hi⟩ : ∃ i, 1 < a i
        . exact ⟨i, Finset.mem_univ i, lemma_2 hx (a i) hi⟩
        by_contra! H
        -- If otherwise, all a i = 1, then M = 1, which contradicts hM.
        replace H i : a i = 1 := (Nat.le_antisymm (H i) (ha i))
        simp only [H, Finset.prod_const_one] at hprod
        simp [← hprod] at hM