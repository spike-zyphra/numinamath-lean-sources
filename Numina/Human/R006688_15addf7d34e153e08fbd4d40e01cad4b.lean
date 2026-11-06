import Mathlib

/-!
For any integer `x ≥ 4`, we show
```
(x - 3)/x < (x - 2)/x < (x - 1)/(x + 1) < (x - 1)/x < (x + 1)/x < (x - 1)/(x - 2)
```
-/
theorem fractions_order {x : ℕ} (h : 4 ≤ x) :
  (x - 3 : ℚ) / x < (x - 2 : ℚ) / x ∧
  (x - 2 : ℚ) / x < (x - 1 : ℚ) / (x + 1) ∧
  (x - 1 : ℚ) / (x + 1) < (x - 1 : ℚ) / x ∧
  (x - 1 : ℚ) / x < (x + 1 : ℚ) / x ∧
  (x + 1 : ℚ) / x < (x - 1 : ℚ) / (x - 2) := by
  -- All relevant denominators are positive
  have hx_pos  : 0 < (x : ℚ)     := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) h)
  have hx1_pos : 0 < (x + 1 : ℚ) := by exact_mod_cast (Nat.succ_pos x)
  have hx2_pos : 0 < (x - 2 : ℚ) := by norm_num; omega


  -- 1) (x - 3)/x < (x - 2)/x
  have h1 : (x - 3 : ℚ) / x < (x - 2 : ℚ) / x := by
    gcongr
    norm_num

  -- 2) (x - 2)/x < (x - 1)/(x+1)
  have h2 : (x - 2 : ℚ) / x < (x - 1 : ℚ) / (x + 1) := by
    rw [div_lt_div_iff₀ hx_pos hx1_pos]
    have h2_1: (↑x - 1) * ↑x - (↑x - 2) * (↑x + 1) > (0: ℚ) := by
      ring_nf
      norm_num
    exact lt_of_sub_pos h2_1

  -- 3) (x - 1)/(x+1) < (x - 1)/x
  have h3 : (x - 1 : ℚ) / (x + 1) < (x - 1 : ℚ) / x := by
    rw [div_lt_div_iff₀ hx1_pos hx_pos]
    have h3_1: (↑x - 1) * (↑x + 1) - (↑x - 1) * ↑x > (0: ℚ) := by
      ring_nf
      norm_num
      omega
    exact lt_of_sub_pos h3_1

  -- 4) (x - 1)/x < (x + 1)/x
  have h4 : (x - 1 : ℚ) / x < (x + 1 : ℚ) / x := by
    gcongr
    linear_combination

  -- 5) (x + 1)/x < (x - 1)/(x-2)
  have h5 : (x + 1 : ℚ) / x < (x - 1 : ℚ) / (x - 2) := by
    rw [div_lt_div_iff₀ hx_pos hx2_pos]
    have h5_1: (0: ℚ) < (↑x - 1) * ↑x  - (↑x + 1) * (↑x - 2)  := by
      ring_nf
      norm_num
    exact lt_of_sub_pos h5_1

  exact ⟨h1, h2, h3, h4, h5⟩
