import Mathlib

/- 14. If $x^{3}+x^{2}+2 x+2=0$, then

$$

x^{-2008}+x^{-2006}+\cdots+x^{-4}+x^{-2}+1+x+x^{3}+\cdots+x^{2005}+x^{2007}+x^{2009}

$$
 -/
theorem algebra_119673 {x : ℝ} (hx : x^3 + x^2 + 2 * x + 2 = 0) :
    ∑ i ∈ Finset.range 1005, x^(-2 * i : ℤ) + ∑ i ∈ Finset.range 1005, x ^ (2 * i + 1) = 0 := by
  -- prove that x = -1
  replace hx : x = -1 := by
    -- x^3 + x^2 + 2 * x + 2 = 0 can be rewritten as (x ^ 2 + 2) * (x + 1) = 0
    have eq : (x ^ 2 + 2) * (x + 1) = 0 := by linear_combination hx
    -- so x ^ 2 + 2 = 0 or x + 1 = 0
    rw [mul_eq_zero] at eq
    cases eq with
    -- x ^ 2 + 2 = 0 is impossible since x ^ 2 ≥ 0 and 2 > 0
    | inl h => nlinarith
    -- x + 1 = 0 implies x = -1
    | inr h => linarith
  rw [hx]
  -- (-1) ^ (2 * n + 1) = -1 for any natural n
  have hpow_odd n : (-1 : ℝ) ^ (2 * n + 1) = -1 := by norm_num
  -- (-1) ^ (-2 * n) = 1 for any integer n
  have hpow_even (n : ℤ) : (-1 : ℝ) ^ (-2 * n) = 1 := by
    rw [Int.neg_mul_comm, zpow_mul]
    norm_num
  -- we get 1005 * 1 + 1005 * (-1) = 0
  simp_rw [hpow_even, hpow_odd, Finset.sum_const, Finset.card_range]
  norm_num