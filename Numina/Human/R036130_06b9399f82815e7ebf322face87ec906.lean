import Mathlib

/-
  For every positive integer $n$, let

  $$
  x_{n}=\frac{(2 n+1) \cdot(2 n+3) \cdots \cdots \cdot(4 n-1) \cdot(4 n+1)}{2 n \cdot(2 n+2) \cdots \cdots \cdot(4 n-2) \cdot 4 n}
  $$

  Prove that $\frac{1}{4 n}< x_{n}-\sqrt{2}<\frac{2}{n}$.
-/
theorem inequalities_604725 {n : ℕ} (hn : n > 0) {x : ℝ}
    (hx : x = (∏ i ∈ Finset.range (n + 1), (2 * n + 2 * i + 1)) / ∏ i ∈ Finset.range (n + 1), (2 * n + 2 * i)) : 1 / (4 * n) < x - Real.sqrt 2 ∧ x - Real.sqrt 2 < 2 / n := by
  -- prove a transformation, (∏ i ∈ Finset.range (n + 1), f i) ^ 2 = f 0 * f n * ∏ i ∈ Finset.range n, f i * f (i + 1)
  have heq {f : ℕ → ℝ} : (∏ i ∈ Finset.range (n + 1), f i) ^ 2 = f 0 * f n * ∏ i ∈ Finset.range n, f i * f (i + 1) := by
    rw [Finset.prod_mul_distrib, sq]
    nth_rw 1 [Finset.prod_range_succ]
    rw [Finset.prod_range_succ']
    ring
  -- prove x(x+2) \leqslant (x+1)^{2}
  have hle (x : ℝ) : x * (x + 2) ≤ (x + 1) ^ 2 := by rw [mul_add, add_sq]; ring_nf; simp
  -- Squaring both sides of the given equality and applying $x(x+2) \leqslant (x+1)^{2}$ to the numerator of the obtained fraction and cancelling we have
  -- $$x_{n}^{2} \leqslant \frac{(2 n+1) \cdot (4 n+1)}{(2 n)^{2}}2 + \frac{1}{n} $$
  have hxle : x ^ 2 ≤ 8 * ((n + 1) / (2 * n)) ^ 2  := by
    calc
      x ^ 2 = _ := by rw [hx]
      _ = (2 * n + 1) * (4 * n + 1) * ↑(∏ i ∈ Finset.range n, (2 * n + 2 * i + 1) * (2 * n + 2 * i + 1 + 2)) / (∏ i ∈ Finset.range (n + 1), (2 * n + 2 * i)) ^ 2 := by
        -- apply the transformation
        rw [div_pow]
        simp
        simp [heq]
        congr
        · ring
        · ext x; ring
      _ ≤ (2 * n + 1) * (4 * n + 1) * ↑(∏ i ∈ Finset.range n, (2 * n + 2 * (i + 1))) ^ 2 / (∏ i ∈ Finset.range (n + 1), (2 * n + 2 * i)) ^ 2 := by
        -- apply x(x+2) \leqslant (x+1)^{2}
        apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · simp [←Finset.prod_pow]
            apply Finset.prod_le_prod
            · intro i _
              norm_cast
              apply mul_nonneg
              · norm_num
              · norm_num
            · intro i _
              apply le_trans (hle _)
              apply le_of_eq
              ring
          · norm_cast
            simp
        · norm_cast
          apply sq_nonneg _
      _ = (2 * n + 1) * (4 * n + 1) / (2 * n) ^ 2 := by
        rw [Finset.prod_range_succ']
        simp
        rw [mul_pow, div_mul_eq_div_div, mul_div_cancel_right₀]
        apply ne_of_gt
        apply sq_pos_of_pos
        norm_cast
        simp
      _ ≤ _ := by
        rw [div_pow, ←mul_div_assoc]
        apply div_le_div_of_nonneg_right
        · ring_nf
          simp
          apply add_le_add
          · norm_num
          · apply mul_le_mul_of_nonneg_left
            · norm_num
            · simp [hn]
        · apply sq_nonneg
  -- similarly, x² ≥ (4n+1)²/(8n²)
  have hxge : x ^ 2 ≥ (4 * n + 1) ^ 2 / (8 * n ^ 2) := by
    calc
      x ^ 2 = _ := by rw [hx]
      _ = ↑(∏ i ∈ Finset.range (n + 1), (2 * n + 2 * i + 1)) ^ 2 / ((2 * n) * (4 * n) * ∏ i ∈ Finset.range n, (2 * n + 2 * i) * (2 * n + 2 * i + 2)) := by
        -- apply the transformation
        rw [div_pow]
        simp
        simp [heq]
        congr
        · ring
        · ext; ring
      _ ≥ ↑(∏ i ∈ Finset.range (n + 1), (2 * n + 2 * i + 1)) ^ 2 / ((2 * n) * (4 * n) * ∏ i ∈ Finset.range n, ↑(2 * n + 2 * i + 1) ^ 2) := by
        -- apply x(x+2) \leqslant (x+1)^{2}
        apply div_le_div_of_nonneg_left
        · apply sq_nonneg
        · norm_cast
          simp [hn]
        · apply mul_le_mul_of_nonneg_left
          · simp
            apply Finset.prod_le_prod
            · intro i _
              norm_cast
              apply Nat.zero_le
            · intro i _
              apply le_trans (hle _)
              rfl
          · norm_cast
            apply Nat.zero_le
      _ = (4 * n + 1) ^ 2 / (8 * n ^ 2) := by
        nth_rw 2 [mul_comm]
        rw [div_mul_eq_div_div, Finset.prod_range_succ]
        simp
        rw [mul_pow, Finset.prod_pow, mul_div_cancel_left₀]
        · ring
        · apply ne_of_gt
          apply sq_pos_of_pos
          norm_cast
          simp

  -- prove x ≥ 0
  have hxnonneg : x ≥ 0 := by
    simp [hx]
    apply div_nonneg
    all_goals {
      apply Finset.prod_nonneg
      intro _ _
      norm_cast
      apply Nat.zero_le
    }

  constructor
  · -- 1 / (4 n) < 1 / (2√2 n) < x - √ 2
    calc
      _ < 1 / (2 * √ 2 * n) := by
        apply div_lt_div_of_pos_left
        · norm_num
        · simp [hn]
        · apply mul_lt_mul_of_pos_right
          · rw [show (4 : ℝ) = 2 * 2 by norm_num]
            simp
            refine (Real.sqrt_lt' ?h.bc.hy).mpr ?h.bc.a
            all_goals norm_num
          · simp [hn]
      _ = √ ((4 * n + 1) ^ 2 / (8 * n ^ 2)) - √ 2 := by
        rw [Real.sqrt_div, Real.sqrt_sq, Real.sqrt_mul (by simp [hn]), Real.sqrt_sq (by simp [hn]), div_sub']
        · congr
          · ring_nf
            rw [mul_assoc, ←mul_sub]
            simp [show ¬ n = 0 by apply ne_of_gt hn]
            apply sub_eq_zero.mpr
            rw [←Real.sqrt_mul (by norm_num), show (8 * 2 = (4 : ℝ) ^ 2) by norm_num, Real.sqrt_sq (by norm_num)]
          · rw [show (8 : ℝ) = (2 ^ 2) * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
        · apply ne_of_gt
          simp [hn]
        · norm_cast
          apply Nat.zero_le
        · apply sq_nonneg
      _ ≤ √ (x ^ 2) - √ 2 := by rel [hxge]
      _ = x - √ 2 := by rw [Real.sqrt_sq hxnonneg]
  · -- x - √ 2 ≤ √(8 * ((n + 1) / (2 * n)) ^ 2) - √ 2 = √ 2 / n < 2 / n
    calc
      _ = √ (x ^ 2) - √ 2 := by rw [Real.sqrt_sq hxnonneg]
      _ ≤ √ (8 * ((n + 1) / (2 * n)) ^ 2) - √ 2 := by rel [hxle]
      _ = √ (2 * ((n + 1) / n) ^ 2) - √ 2 := by
        congr 2
        ring
      _ = √ 2 / n := by
        rw [Real.sqrt_mul, Real.sqrt_sq]
        · field_simp
          ring
        · apply div_nonneg
          all_goals {
            norm_cast
            apply Nat.zero_le
          }
        · norm_cast
      _ < 2 / n := by
        apply div_lt_div_of_pos_right
        · apply Real.sqrt_lt' ?_ |>.mpr
          all_goals norm_num
        · simp [hn]
