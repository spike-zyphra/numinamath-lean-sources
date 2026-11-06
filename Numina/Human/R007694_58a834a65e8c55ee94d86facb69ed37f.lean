import Mathlib

open Real

/- Let $a$ and $b$ be real numbers greater than 1 such that $a b=100$. The maximum possible value of $a^{\left(\log _{10} b\right)^{2}}$ can be written in the form $10^{x}$ for some real number $x$. Find $x$.-/
theorem algebra_609926 {s : Set ℝ} (hs : s = {y : ℝ | ∃ a b : ℝ, 1 < a ∧ 1 < b ∧ a * b = 100 ∧ y = a ^ ((logb 10 b) ^ 2)})
    {x : ℝ} (hx : IsGreatest s (10 ^ x)) : x = 32 / 27 := by
  -- It's clear that `f(x)=10^x` is injective.
  have rpow_right_injective : Function.Injective (fun x : ℝ => (10 : ℝ) ^ x) := by
    intro a b h
    rw [← mul_right_inj' (by positivity : log 10 ≠ 0)]
    apply exp_injective
    rw [exp_mul, exp_log (by norm_num), exp_mul, exp_log (by norm_num)]
    exact h
  -- Since `f(x)=10^x` is injective, suffices to show `10 ^ x = 10 ^ (32 / 27)`.
  apply rpow_right_injective
  beta_reduce
  -- By the uniqueness of `IsGreatest`, suffices to show maximum of `s` is `10 ^ (32 / 27)`.
  suffices IsGreatest s ((10 : ℝ) ^ (32 / 27 : ℝ)) from hx.unique this
  rw [hs]
  -- We split into two cases.
  constructor
  . -- Verify that `10 ^ (32 / 27)` can be achieved.
    use (10 : ℝ) ^ (2 / 3 : ℝ), (10 : ℝ) ^ (4 / 3 : ℝ)
    split_ands
    . exact one_lt_rpow (by norm_num) (by norm_num)
    . exact one_lt_rpow (by norm_num) (by norm_num)
    . rw [← rpow_add (by norm_num)]; norm_num
    . rw [logb_rpow (by norm_num) (by norm_num), ← rpow_mul (by norm_num)]; congr; norm_num
  . -- Show `10 ^ (32 / 27)` is the largest.
    intro y ⟨a, b, ha, hb, hab, hy⟩
    -- Need positivity of `y` to perform simplification `10^{log_{10} y} = y`.
    have ypos : 0 < y := by rw [hy]; positivity
    rw [← Real.rpow_logb (b := 10) (x := y) (by norm_num) (by norm_num) (by positivity),
      Real.rpow_le_rpow_left_iff (by norm_num)]
    -- Let `p` equals `log_{10} a`.
    set p := logb 10 a with hp
    -- Let `q` equals `log_{10} b`.
    set q := logb 10 b with hq
    -- Let `x` equals `log_{10} y`.
    set x := logb 10 y with hx
    -- Need positivity of `p` to perform simplification `10^{log_{10} p} = p`.
    have ppos : 0 < p := by rw [hp]; exact logb_pos (by norm_num) ha
    -- Need positivity of `q` to perform simplification `10^{log_{10} q} = q`.
    have qpos : 0 < q := by rw [hq]; exact logb_pos (by norm_num) hb
    -- Since `ab=100` we have `p+q=2`.
    have addpq : p + q = 2 := by
      apply rpow_right_injective
      beta_reduce
      rw [rpow_add (by norm_num), hp, rpow_logb (by norm_num) (by norm_num) (by positivity),
        hq, rpow_logb (by norm_num) (by norm_num) (by positivity), hab]
      norm_num
    -- It's clear that `x=pq^2` by assumption.
    have xeq : x = p * q ^ 2 := by
      apply rpow_right_injective
      beta_reduce
      rwa [hx, rpow_logb (by norm_num) (by norm_num) (by positivity), rpow_mul (by norm_num),
        hp, rpow_logb (by norm_num) (by norm_num) (by positivity)]
    have xpow : 0 < x := by rw [xeq]; positivity
    -- Need the following lemmas to use AM-GM inequality.
    have h1 : 0 ≤ (1 / 3 : ℝ) := by norm_num
    have h2 : 0 ≤ p := by positivity
    have h3 : 0 ≤ q / 2 := by positivity
    -- Use AM-GM inequality, we have `x^{1/3} / 2^{2/3} ≤ 2/3`.
    have : x ^ (1 / 3 : ℝ) * (2⁻¹ : ℝ) ^ (1 / 3 : ℝ) * (2⁻¹ : ℝ) ^ (1 / 3 : ℝ) ≤ 2 / 3 := by
      convert geom_mean_le_arith_mean3_weighted h1 h1 h1 h2 h3 h3 (by norm_num) using 1
      . rw [xeq, mul_rpow (by positivity) (by positivity), div_eq_mul_inv q 2,
          mul_rpow (by positivity) (by positivity), pow_two, mul_rpow (by positivity) (by positivity)]
        ring
      . nth_rw 1 [← addpq]
        ring
    -- Cube both side of inequality, we have `x / 4 ≤ 8 / 27`
    rw [← pow_le_pow_iff_left₀ (n := 3) (by positivity) (by positivity) (by norm_num),
      mul_pow, mul_pow, ← rpow_natCast,
      ← rpow_mul (by positivity), ← rpow_natCast, ← rpow_mul (by norm_num),
      show (1 / 3 : ℝ) * ↑(3 : ℕ) = 1 by norm_num] at this
    norm_num at this
    -- Hence we have `x ≤ 32 / 27` which is desired.
    linarith
