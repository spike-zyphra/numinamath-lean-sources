import Mathlib

/- 2. Let $a, b, c, A, B, C$ be non-negative real numbers such that

$$
a+A=b+B=c+C=k .
$$

Prove that

$$
a B+b C+c A \leq k^{2}
$$ -/
theorem inequalities_220028 (a b c A B C k : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hak : a + A = k) (hbk : b + B = k) (hck : c + C = k) :
    a * B + b * C + c * A ≤ k ^ 2 := by
  -- We unfold `k ^ 3` into `(a + A)(b + B)(c + C)` which we can then rewrite into
  -- `abc + ABC + k(cA + bC + aB)`.
  -- The first two terms are non-negative, so we end up with `k ^ 3 ≥ k(aB + bC + cA)`
  have := calc
    k ^ 3 = (a + A) * (b + B) * (c + C) := by rw [hak, hbk, hck]; ring
    _ = a * b * c + A * B * C + c * A * (b + B) + b * C * (a + A) + a * B * (c + C) := by ring
    _ = a * b * c + A * B * C + c * A * k + b * C * k + a * B * k := by rw [hak, hbk, hck]
    _ = a * b * c + A * B * C + k * (a * B + b * C + c * A) := by ring
    _ ≥ 0 + 0 + k * (a * B + b * C + c * A) := by gcongr <;> positivity
    _ = k * (a * B + b * C + c * A) := by ring
  rw [pow_succ'] at this
  -- We cancel the `k` on both sides to get the desired inequality.
  -- However, this only works if `k` is positive
  by_cases hk : 0 < k 
  · rw [ge_iff_le, mul_le_mul_left hk] at this
    exact this
  · -- If `k` is not positive, it's zero
    obtain rfl : k = 0 := by linarith
    -- Substitute `k` and then `a`, `b` and `c`
    rw [add_eq_zero_iff_eq_neg] at hak hbk hck
    rcases hak with rfl; rcases hbk with rfl; rcases hck with rfl
    -- Now the inequality is obvious by the non-negativity assumptions
    rw [← neg_le_neg_iff]
    ring_nf
    positivity
      
#check neg_le_neg_iff
