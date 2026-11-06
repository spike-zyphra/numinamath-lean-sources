import Mathlib

open Real

/- Let, $f(x) = (x^2 + 3x + 2)^{\cos(\pi x)}$. Find the sum of all positive integers $n$ for which
$$\left|\sum_{k=1}^{n} \log_{10} f(k) \right| = 1.$$ -/
theorem algebra_96104 {f : ℕ → ℝ}
    (hf : ∀ x, f x = (x^2 + 3 * x + 2) ^ cos (π * x)) :
    ∑ᶠ n ∈ {n | 0 < n ∧ |∑ k in Finset.Icc 1 n, logb 10 (f k)| = 1}, n = 21 := by
  -- if x is even (i.e., x = 2 * k) then f x = (x + 1) * (x + 2)
  -- this follows from the fact that cos(pi * x) = 1 when x is even
  have hf_even : ∀ k, f (2 * k) = (2 * k + 1) * (2 * k + 2) := by
    intro k; rw [hf]; push_cast
    rw [show π * (2 * k) = k * (2 * π) by linarith, cos_nat_mul_two_pi, rpow_one]
    ring
  -- if x is odd (i.e., x = 2 * k + 1) then f x = 1 / ((x + 1) * (x + 2))
  -- this follows from the fact that cos(pi * x) = -1 when x is odd
  have hf_odd : ∀ k, f (2 * k + 1) = 1 / ((2 * k + 2) * (2 * k + 3)) := by
    intro k; rw [hf]; push_cast
    rw [show π * (2 * k + 1) = k * (2 * π) + π by linarith, cos_nat_mul_two_pi_add_pi]
    rw [rpow_neg_one, one_div]
    congr; ring
  -- prove that 0 < f k for all k (this fact will be used later)
  have hf_pos : ∀ k, 0 < f k := by
      intro k
      obtain ⟨k', hk'⟩ := Nat.even_or_odd' k
      rcases hk' with hk' | hk' <;> rw [hk']
      · rw [hf_even]; positivity
      · rw [hf_odd]; positivity
  -- the sum of logarithms of (f k) is the logarithm of the product of (f k)
  have hsum_eq : ∀ n > 0, ∑ k in Finset.Icc 1 n, logb 10 (f k) = logb 10 (∏ k in Finset.Icc 1 n, f k) := by
    intro n hn
    refine Eq.symm (logb_prod (Finset.Icc 1 n) f ?_)
    intro k _; exact ne_of_gt (hf_pos k)
  -- when the upper bound of the product range is even and positive (i.e., 2 * (n + 1) for some n) then
  -- the product is equal to n + 2
  have hprod_even : ∀ n : ℕ, ∏ k in Finset.Icc 1 (2 * (n + 1)), f k = n + 2 := by
    intro n
    -- proof by induction
    induction n with
    | zero => simp [Finset.prod_Icc_succ_top, hf_even 1, hf_odd 0]; norm_num
    | succ n ih =>
      rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 by omega]
      rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega), ih]
      rw [hf_odd, show 2 * (n + 1) + 1 + 1 = 2 * (n + 2) by omega, hf_even]
      field_simp; ring
  -- when the upper bound of the product range is odd (i.e., 2 * n + 1 for some n) then
  -- the product is equal to 1 / (2 * (2 * n + 3))
  have hprod_odd : ∀ n : ℕ, ∏ k in Finset.Icc 1 (2 * n + 1), f k = 1 / (2 * (2 * n + 3)) := by
    intro n
    -- proof by induction
    induction n with
    | zero => simp [Finset.prod_Icc_succ_top, hf_odd 0]
    | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
      rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega), ih]
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, hf_even, hf_odd]
      field_simp; ring
  -- it is left to show that the set over which the sum is taken equals to {3, 18}
  suffices {n | 0 < n ∧ |∑ k ∈ Finset.Icc 1 n, logb 10 (f k)| = 1} = {3, 18} by
    rw [this, finsum_mem_eq_toFinset_sum]; simp
  -- prove that logb 10 x = 1 ↔ x = 10 (this simple fact is missing in Mathlib)
  have logb_eq_one x (hx : x > 0) : (logb 10 x = 1 ↔ x = 10) := by
    constructor
    · intro h
      apply Real.logb_injOn_pos (show (1 : ℝ) < 10 by norm_num) hx (by simp)
      rw [logb_self_eq_one (by norm_num), h]
    · intro h; rw [h, logb_self_eq_one (by norm_num)]
  -- prove that logb 10 x = -1 ↔ x = 1 / 10 (this simple fact is missing in Mathlib)
  have logb_eq_neg_one x (hx : x > 0) : logb 10 x = -1 ↔ x = 1 / 10 := by
    constructor
    · intro h
      apply Real.logb_injOn_pos (show (1 : ℝ) < 10 by norm_num) hx (by simp)
      rw [h, one_div, logb_inv, logb_self_eq_one (by norm_num)]
    · intro h; rw [h, one_div, logb_inv, logb_self_eq_one (by norm_num)]
  -- demonstrate the equality of two sets
  ext n; simp
  symm; constructor
  · intro hn
    have hn_pos : 0 < n := by omega
    refine ⟨hn_pos, ?_⟩
    -- if |x| = 1 then x = 1 or x = -1
    rw [hsum_eq n hn_pos, abs_eq zero_le_one]
    cases hn with
    | inl hn =>
      -- when n = 3 then the product is equal to 10 and logb 10 10 = 1
      right; rw [hn, hprod_odd 1]; norm_num
      rw [logb_eq_neg_one]; norm_num
    | inr hn =>
      -- when n = 18 then the product is equal to 1 / 10 and logb 10 (1 / 10) = -1
      left; rw [hn, hprod_even 8]; norm_num
  · intro ⟨hn_pos, heq⟩; revert heq
    rw [hsum_eq n hn_pos, abs_eq zero_le_one]
    -- we need to show that the product is positive in order to use
    -- assumptions logb_eq_one and logb_eq_neg_one
    have hprod_pos : ∀ n > 0, ∏ k ∈ Finset.Icc 1 n, f k > 0 := by
      intro n hn
      apply Finset.prod_pos
      intro i _; exact hf_pos i
    -- since 0 < n, we have n = 2 * (k + 1) or n = 2 * k + 1 for some k
    have ⟨k, hk⟩ : ∃ k, n = 2 * (k + 1) ∨ n = 2 * k + 1 := by
      obtain ⟨k, hk⟩ := Nat.even_or_odd' n
      rcases hk with hk | hk
      · use k - 1; left; omega
      · use k; right; assumption
    intro h
    cases h with
    | inl h =>
      -- if logb 10 of the product is 1 then show that n = 18
      rw [logb_eq_one _ (hprod_pos _ hn_pos)] at h
      rcases hk with hk | hk
      · rw [hk, hprod_even] at h; norm_cast at h
        right; omega
      · rw [hk, hprod_odd] at h
        suffices (1 : ℝ) / (2 * (2 * k + 3)) < 1 by linarith
        rw [div_lt_one (by linarith)]
        linarith
    | inr h =>
      -- if logb 10 of the product is -1 then show that n = 3
      rw [logb_eq_neg_one _ (hprod_pos _ hn_pos)] at h
      rcases hk with hk | hk
      · rw [hk, hprod_even] at h
        linarith
      · rw [hk, hprod_odd] at h
        left
        apply eq_of_one_div_eq_one_div at h
        norm_cast at h; omega