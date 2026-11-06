import Mathlib

/- Solve for $x$: $$\dfrac{66-2^x}{2^x+3}=\dfrac{4-2^x}{2^{x+1}+6}$$ -/
theorem algebra_20614 {x : ℕ} : (66 - 2 ^ x : ℝ) / (2 ^ x + 3) = (4 - 2 ^ x) / (2 ^ (x + 1) + 6) → x = 7 := by
  intro h
  -- First, we recognize that $2^{x+1}+6=2(2^x+3)$
  have h1 : (2 : ℝ) ^ (x + 1) + 6 = 2 * (2 ^ x + 3) := by
    ring
  -- $\dfrac{2(66-2^x)}{2(2^x+3)}=\dfrac{4-2^x}{2(2^x+3)}$
  rw [h1] at h
  have h2 : (66 - 2 ^ x : ℝ) / (2 ^ x + 3) = 2 * (66 - 2 ^ x : ℝ) / (2 * (2 ^ x + 3)) := by
    calc
      _ = (66 - 2 ^ x : ℝ) / (2 ^ x + 3) * 2 / 2 := by ring
      _ = 2 * (66 - 2 ^ x : ℝ) / (2 ^ x + 3) / 2 := by ring
      _ = 2 * (66 - 2 ^ x : ℝ) / ((2 ^ x + 3) * 2) := by
        exact div_div (2 * (66 - 2 ^ x)) (2 ^ x + 3) 2
      _ = _ := by ring
  rw [h2] at h
  -- Then, we expand and collect like terms: $\dfrac{128-2^x}{2(2^x+3)} = 0$
  apply sub_eq_zero_of_eq at h
  rw [← sub_div] at h
  -- This equation can only be true when $2^x = 128$
  have ne : (2 : ℝ) ^ x + 3 ≠ 0 := by
    have gt : 0 < (2 : ℝ) ^ x + 3 := by
      apply add_pos_of_pos_of_nonneg
      refine pow_pos ?_ x
      exact zero_lt_two
      exact zero_le_three
    exact Ne.symm (ne_of_lt gt)
  simp only [div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ne, or_self, or_false] at h
  ring_nf at h
  have h3 : (2 : ℝ) ^ x = 2 ^ 7 := by
    linarith
  -- So $x = 7$
  apply pow_right_injective at h3
  exact h3
  exact zero_lt_two
  exact Ne.symm (OfNat.one_ne_ofNat 2)
