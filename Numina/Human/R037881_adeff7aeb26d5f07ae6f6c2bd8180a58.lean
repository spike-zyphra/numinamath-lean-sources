import Mathlib

theorem algebra_195684 (hn : 2 ≤ n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a ^ n = a + 1) (h2 : b ^ (2 * n) = b + 3 * a) : 1 < b ∧ b < a := by
  replace ha : 1 < a := by
    by_contra!; suffices : a ^ n ≤ 1
    · linarith only [this, h1, ha]
    rw [pow_le_one_iff_of_nonneg]; exact this
    linarith only [ha]; omega
  replace hb : 1 < b := by
    by_contra!; suffices : b ^ (2 * n) ≤ 1
    · linarith only [this, h2, ha, hb]
    rw [pow_le_one_iff_of_nonneg]; exact this
    linarith only [hb]; omega
  by_cases h : a = b
  · rw [h] at h1 h2; rw [mul_comm, pow_mul] at h2
    rw [h1, ← sub_eq_zero] at h2
    simp [show (b + 1) ^ 2 - (b + 3 * b) = (b - 1) ^ 2 by ring] at h2
    linarith only [h2, hb]
  rw [← div_eq_one_iff_eq, ← ne_eq] at h
  have := geom_sum_eq h (2 * n)
  rw [div_pow, div_sub_one, div_sub_one, div_div_div_eq] at this
  nth_rw 3 [mul_comm] at this; rw [pow_mul, h1] at this
  nth_rw 1 [h2] at this; nth_rw 2 [mul_comm] at this
  rw [show 2*n = 1+(2*n-1) by omega, Finset.sum_range_add] at this
  rw [pow_add, pow_one, mul_assoc, mul_div_mul_left] at this
  nth_rw 3 [mul_comm] at this; rw [div_mul_eq_div_mul_one_div] at this
  rw [← div_eq_iff, div_div_eq_mul_div, div_one, add_mul] at this
  simp [show (a+1)^2-(b+3*a) = (a-1)^2+(a-b) by ring] at this
  rw [← div_add_one, ← sub_eq_iff_eq_add] at this
  rw [add_sub_right_comm] at this
  replace this : 0 < (a - 1) ^ 2 / (a - b) := by calc
    _ < b ^ (2 * n - 1) - 1 := by
      rw [sub_pos, one_lt_pow_iff_of_nonneg]; exact hb
      linarith only [hb]; omega
    _ < _ := by
      rw [← this, lt_add_iff_pos_right]
      apply mul_pos; apply Finset.sum_pos
      · intros; apply pow_pos; apply div_pos
        linarith only [ha]; linarith only [hb]
      · use 0; simp; omega
      apply pow_pos; linarith only [hb]
  rw [div_pos_iff_of_pos_left] at this
  exact ⟨hb, by linarith only [this]⟩
  apply pow_pos; linarith only [ha]
  · intro h'; rw [sub_eq_zero] at h'; rw [h', div_self] at h
    contradiction; linarith only [hb]
  · simp; intro h; linarith only [h, hb]
  any_goals linarith only [hb]
  positivity