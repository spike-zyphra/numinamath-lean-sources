import Mathlib

open Finset Real Nat

/- Let $x_{1}, x_{2}, \ldots, x_{n}$ be positive real numbers, and let

$$
S=x_{1}+x_{2}+\cdots+x_{n}
$$

Prove that

$$
\left(1+x_{1}\right)\left(1+x_{2}\right) \cdots\left(1+x_{n}\right) \leq 1+S+\frac{S^{2}}{2!}+\frac{S^{3}}{3!}+\cdots+\frac{S^{n}}{n!}
$$ -/
theorem inequalities_604152 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ i ∈ range n, 0 < x i) (S : ℝ) (hS : S = ∑ i ∈ range n, x i) :
    ∏ i ∈ range n, (1 + x i) ≤ ∑ i ∈ range (n + 1), S ^ i / (Nat.factorial i) := by
  -- prove by induction
  induction n, hn using Nat.le_induction generalizing S
  · -- n = 1, trivial
    simp at hS ⊢
    rw [sum_range_succ, sum_range_succ]
    simp [hS]
  · -- let S' := S - x n, i.e., x0 + ... + x(n-1)
    rename_i n hn ih
    rw [prod_range_succ]
    let S' := ∑ i ∈ range n, x i
    have hS'_pos : S' > 0 := by
      apply sum_pos
      · intro i hi
        apply hx
        simp at hi ⊢
        apply lt_trans hi
        simp
      · simp
        exact not_eq_zero_of_lt hn
    -- LFS ≤ ∑ i ∈ range (n + 1), S' ^ i / (Nat.factorial i) * (1 + x n) by I.H.
    trans (∑ i ∈ range (n + 1), S' ^ i / ↑i !) * (1 + x n)
    · gcongr
      · apply add_nonneg
        · positivity
        · apply le_of_lt
          apply hx
          simp
      · apply ih
        · intro i hi
          apply hx
          simp at hi ⊢
          apply lt_trans hi
          simp
        · rfl
    rw [mul_add, mul_one]
    -- It suffices to show that ∑ i ∈ range (n + 1), S' ^ i / (Nat.factorial i) * (1 + x n) ≤ RHS
    -- Note that ∑ i ∈ range (n + 1), S' ^ i / (Nat.factorial i) * (1 + x n) ≤ 1 + ∑ i ∈ [0, n], (S' ^ (i + 1) / (Nat.factorial (i + 1)) + S' ^ i / (Nat.factorial i) * x n)
    trans 1 + ∑ i ∈ range (n + 1), ((S' ^ (i + 1) / (i + 1) !) + (x n * S' ^ i) / i !)
    · rw [sum_add_distrib, ←add_assoc]
      gcongr
      · rw [sum_range_succ']
        rw [add_comm]
        simp
        apply sum_le_sum_of_subset_of_nonneg
        · simp
        · intro _ _ _
          apply div_nonneg
          · apply pow_nonneg
            positivity
          · apply le_of_lt
            positivity
      · rw [mul_comm, mul_sum]
        gcongr
        rw [mul_div_assoc]
    -- therefore, it suffices to show that
    -- 1 + ∑ i ∈ [0, n], S' ^ (i + 1) / (Nat.factorial (i + 1)) + S' ^ i / (Nat.factorial i) * x n ≤ RHS = 1 + ∑ i ∈ [0, n], S ^ (i + 1) / (Nat.factorial (i + 1))
    rw [sum_range_succ' _ (n + 1), add_comm]
    simp
    gcongr
    -- or equivalently, S' ^ (i + 1) + (i + 1) * ∑ i, S' ^ i * x n ≤ S ^ (i + 1)
    -- which is followed by the fact that S = S' + x n and the Bernoulli's inequality
    apply le_div_iff₀ ?_ |>.mpr
    · rw [add_mul, div_mul_cancel₀, Nat.factorial_succ, cast_mul]
      nth_rw 3 [mul_comm]
      rw [←mul_assoc, div_mul_cancel₀]
      · have hS : S = S' + x n := by
          rw [hS]
          exact sum_range_succ x n
        rw [hS, add_pow, sum_range_succ, sum_range_succ]
        simp
        rw [add_comm]
        nth_rw 2 [mul_comm]
        rw [add_assoc]
        simp
        apply sum_nonneg
        intro _ _
        apply mul_nonneg
        · apply mul_nonneg
          · positivity
          · apply pow_nonneg
            apply le_of_lt
            apply hx
            simp
        · positivity
      · positivity
      · positivity
    · positivity
