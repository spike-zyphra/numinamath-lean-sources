import Mathlib

/- 26. S4 (NZL) Suppose that $x_{1}, x_{2}, x_{3}, \ldots$ are positive real numbers for which  $$ x_{n}^{n}=\sum_{j=0}^{n-1} x_{n}^{j} $$  for $n=1,2,3, \ldots$ Prove that for all $n$,  $$ 2-\frac{1}{2^{n-1}} \leq x_{n}<2-\frac{1}{2^{n}} $$ -/
theorem other_24634 (n : ℕ) (hn : n > 0) (x : ℝ) (h0 : 0 < x) (h1 : x ^ n = ∑ i in Finset.range n, x ^ i) : 2 - 1 / 2 ^ (n - 1) ≤ x ∧ x < 2 - 1 / 2 ^ n := by
  -- Without loss of generality, we can assume n ≥ 2
  wlog h : n ≥ 2
  {
    -- If ¬ n ≥ 2, then n = 1
    -- In this case, x = 1
    -- The inequality is trivially true
    interval_cases n
    simp at h1 ⊢
    subst x
    norm_num
  }
  clear hn

  -- We show that x is the unique solution to the equation x ^ n = ∑ i in Finset.range n, x ^ i where x > 0
  have H (x' : ℝ) (h0' : 0 < x') (h1' : x' ^ n = ∑ i in Finset.range n, x' ^ i) : x = x' := by
    -- Simplify h1 and h1' by dividing by x ^ n and x' ^ n respectively
    apply_fun (· / x ^ n) at h1
    apply_fun (· / x' ^ n) at h1'
    simp [Finset.sum_div, show x ^ n ≠ 0 by positivity] at h1
    simp [Finset.sum_div, show x' ^ n ≠ 0 by positivity] at h1'

    -- Let RHS be f x
    let f (x : ℝ) := ∑ i ∈ Finset.range n, x ^ i / x ^ n
    -- We show that f is strictly decreasing on (0, ∞)
    have H : StrictAntiOn f (Set.Ioi 0) := by
      clear * - h
      intro x hx y hy hxy
      simp at hx hy
      simp only [f]
      -- We prove anti-monotonicity by showing each component is anti-monotonic
      apply Finset.sum_lt_sum_of_nonempty (by simp; linarith)
      intro i hi
      -- Now we need to prove: y ^ i / y ^ n < x ^ i / x ^ n
      simp at hi
      -- Taking the reciprocal of both sides, we need to prove: x ^ n / x ^ i < y ^ n / y ^ i
      rw [← inv_lt_inv (by positivity) (by positivity)]
      simp
      -- Cast the exponents to integers
      suffices H : x ^ (n : ℤ) / x ^ (i : ℤ) < y ^ (n : ℤ) / y ^ (i : ℤ) by norm_cast
      -- Rewrite using a^n / a^m = a^(n - m)
      rw [← zpow_sub₀ (by positivity), ← zpow_sub₀ (by positivity)]
      rw [show (n : ℤ) - i = (n - i : ℕ) from (Mathlib.Tactic.Zify.Nat.cast_sub_of_lt hi).symm]
      -- Cast the exponents back to natural numbers
      norm_cast
      exact pow_lt_pow_left hxy (by positivity) (Nat.sub_ne_zero_iff_lt.2 hi)

    -- Thus, f is injective
    rw [h1] at h1'
    apply StrictAntiOn.injOn at H
    -- And x = x'
    exact H h0 h0' h1'

  -- We will show that there is some x that satisfies the equation
  have ⟨x', hx'1, hx'2, hx'3, hx'4⟩ : ∃ x ∈ Set.Ioi (0 : ℝ), 2 - 1 / 2 ^ (n - 1) ≤ x ∧ x < 2 - 1 / 2 ^ n ∧ x ^ n = ∑ i ∈ Finset.range n, x ^ i := by
    clear h0 h1 H
    -- Let f (x) = (x - 2) * x^n + 1
    -- We will later show that f x = 0 implies x ^ n = ∑ i in Finset.range n, x ^ i
    let f (x : ℝ) := (x - 2) * x^n + 1
    -- First we show that f (2 - 1 / 2 ^ (n - 1)) ≤ 0
    have h1 : f (2 - 1 / 2 ^ (n - 1)) ≤ 0 := by
      -- Simplify the inequality
      simp [f]
      rw [one_le_inv_mul₀ (by positivity),
          pow_sub₀ _ (by simp) (by linarith only [h]),
          ← le_div_iff₀' (by positivity)]
      simp
      rw [show (2 : ℝ) - 2 * (2 ^ n)⁻¹ = (1 - (2 ^ n)⁻¹) * 2 by ring,
          mul_pow]
      simp [show (2 : ℝ) ^ n ≠ 0 by positivity]

      suffices H : (1 - (2 ^ n)⁻¹) ^ n ≥ (1 : ℝ) / 2 by norm_num; linarith only [H]

      -- Now we need to prove (1 - (2 ^ n)⁻¹) ^ n ≥ 1 / 2

      -- We use Bernoulli's inequality to show that (1 - (2 ^ n)⁻¹) ^ n ≥ 1 - n * (2 ^ n)⁻¹
      calc _ ≥ 1 + n * (- (2 ^ n)⁻¹ : ℝ) := one_add_mul_le_pow ?_ _
           _ ≥ 1 / 2 := ?_
      . -- - (2 ^ n)⁻¹ ≥ -2, that is for the condition for Bernoulli's inequality
        simp
        calc (2 ^ n)⁻¹ ≤ (1 : ℝ)⁻¹ := inv_le_inv_of_le (by simp) (one_le_pow_of_one_le (by norm_num))
            _ ≤ 2 := by norm_num
      . -- We still need to show that 1 - n * (2 ^ n)⁻¹ ≥ 1 / 2
        simp
        apply add_le_of_le_sub_left
        norm_num
        rw [mul_inv_le_iff₀ (by positivity)]
        nth_rw 2 [show n = 1 + (n - 1) from (Nat.add_sub_of_le (Nat.one_le_of_lt h)).symm]
        rw [pow_add]
        simp
        -- We simplify the inequality, it suffices to show that n ≤ 2 ^ (n - 1)
        rw [show (2 : ℝ) = 1 + 1 by norm_num]
        -- Use Bernoulli's inequality again
        calc (1 + 1 : ℝ) ^ (n - 1) ≥ 1 + ↑(n - 1) * 1 := one_add_mul_le_pow (by norm_num) _
             _ = n := by norm_cast; simp; exact Nat.add_sub_of_le (Nat.one_le_of_lt h)

    -- Next we show that f (2 - 1 / 2 ^ n) > 0
    have h2 : f (2 - 1 / 2 ^ n) > 0 := by
      -- Simplify the inequality
      simp [f]
      rw [inv_mul_lt_iff (by positivity), mul_one]
      apply pow_lt_pow_left
      . simp
      . -- It suffices to prove that 2 - 1 / 2 ^ n < 2
        simp
        calc (2 ^ n)⁻¹ ≤ (1 : ℝ)⁻¹ := inv_le_inv_of_le (by simp) (one_le_pow_of_one_le (by norm_num))
             _ ≤ 2 := by norm_num
      . linarith only [h]

    -- Also, f is continuous
    have fcont : Continuous f := by continuity

    -- We still have to show that 2 - 1 / 2 ^ (n - 1) ≤ 2 - 1 / 2 ^ n
    have h3 : (2 - 1 / 2 ^ (n - 1) : ℝ) ≤ (2 - 1 / 2 ^ n) := by
      apply sub_le_sub_left
      simp
      rw [inv_le_inv (by positivity) (by positivity)]
      exact pow_le_pow_right (by norm_num) (by simp)

    -- Now, by the intermediate value theorem, there exists x such that f x = 0
    have H := intermediate_value_Ico h3 (Continuous.continuousOn fcont)
    obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := @H 0 ⟨h1, h2⟩

    -- x ≥ 2 - 1 / 2 ^ (n - 1) > 1
    have h0 : x > 1 := by
      calc x ≥ 2 - 1 / 2 ^ (n - 1) := hx1
           _ ≥ 2 - 1 / 2 ^ 1 := sub_le_sub_left (one_div_pow_le_one_div_pow_of_le (by simp) (Nat.le_sub_one_of_lt h)) _
           _ > 1 := by norm_num

    -- We show that x is a solution to the original equation
    refine ⟨x, (by simp; linarith only [h0]), hx1, hx2, ?_⟩
    clear * - h0 hx
    simp only [f] at hx
    -- Expand the geometric sum
    rw [geom_sum_eq (ne_of_gt h0) n]
    -- Simplify the equation and it is equivalent to hx
    field_simp [show x - 1 ≠ 0 by linarith only [h0]]
    linear_combination hx

  -- By uniqueness, x and x' are the same
  -- And we have the desired inequality
  specialize H x' hx'1 hx'4
  subst x
  exact ⟨hx'2, hx'3⟩
