import Mathlib

/- Let $x$ and $y$ be positive real numbers such that $x+y^{2016} \geq 1$. Prove that $x^{2016}+y>$ 1 - 1/100. -/
theorem inequalities_605784 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + y ^ 2016 ≥ 1) : x ^ 2016 + y > 1 - 1 / 100 := by
    by_cases hx' : x ≥ 1 - 1 / (100 * 2016)
    · -- case 1 : x ≥ 1 - 1 / (100 * 2016)
      -- we use Bernoulli's inequality to show x ^ 2016 ≥ 1 - 1 / 100.
      have : x ^ 2016 ≥ 1 - 1 / 100 := by calc
        x ^ 2016 ≥ (1 - 1 / (100 * 2016)) ^ 2016 := by
            apply pow_le_pow_left₀ (by norm_num) hx'
        _ = (1 + (- 1 / (100 * 2016))) ^ 2016 := by ring
        _ ≥ 1 + ↑(2016 : ℕ) * (- 1 / (100 * 2016)) := by
            apply one_add_mul_le_pow
            norm_num
        _ = 1 - 1 / 100 := by ring
      linarith
    · -- case 2 : x < 1 - 1 / (100 * 2016)
      push_neg at hx'

      -- we need the positivity of x ^ 2016 and 1 - x for later use
      have hx_pow_pos : x ^ 2016 > 0 := by exact pow_pos hx 2016
      have hone_sub_x_pos : 1 - x > 0 := by
        calc
          1 - x > 1 / (100 * 2016) := by linarith
          _ > 0 := by norm_num

      -- in this case the goal is to show x ^ 2016 + y ≥ y > 1 - 1 / 100
      suffices h : y > 1 - 1 / 100 by linarith

      -- since y ^ 2016 + x ≥ 1, we deduce y ≥ (1 - x) ^ (1 / 2016)
      have hy_x : y ≥ (1 - x) ^ (1 / 2016 : ℝ) := by
        have : y = (y ^ (2016 : ℝ)) ^ (1 / 2016 : ℝ) := by
          rw [← Real.rpow_mul (by linarith)]
          simp
        rw [this]
        suffices h : y ^ 2016 ≥ 1 - x by
          apply Real.rpow_le_rpow
          linarith
          norm_cast
          linarith
        linarith

      -- we can now change the goal to (1 - x) ^ (1 / 2016) ≥ 1 - 1 / 100
      suffices h : (1 - x) ^ (1 / 2016 : ℝ) > 1 - 1 / 100 by linarith

      -- in this case we have x ≤ 1 - (1 / (100 * 2016)), i.e. (1 - x) ≥ 1 / (100 * 2016),
      -- so we substitute this to change the goal as follows
      suffices h : (1 / (100 * 2016) : ℝ) ^ (1 / 2016 : ℝ) > 1 - 1 / 100 by
        have : 1 - x ≥ 1 / (100 * 2016) := by linarith
        calc
          (1 - x) ^ (1 / 2016 : ℝ) ≥ (1 / (100 * 2016)) ^ (1 / 2016 : ℝ) := by
            apply Real.rpow_le_rpow
            norm_num
            linarith
            norm_num
          _ > 1 - 1 / 100 := h

      -- we can write (1 / (100 * 2016)) ^ (1 / 2016) as (100 * 2016) ^ (-1 / 2016)
      have : (1 / (100 * 2016) : ℝ) ^ (1 / 2016 : ℝ) = (100 * 2016 : ℝ) ^ (-(1 / 2016) : ℝ) := by
        rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
        congr
        exact one_div (100 * 2016)
      rw [this]

      -- now the goal becomes (100 * 2016) ^ (-(1 / 2016)) > 1 - 1 / 100
      -- take power of -2016 on both sides, it is equivalent to show that
      -- 100 * 2016 < (1 - 1 / 100) ^ (-2016)
      suffices h : (100 * 2016 : ℝ) < (1 - 1 / 100) ^ (-2016 : ℝ) by
        have : (1 - 1 / 100 : ℝ) = ((1 - 1 / 100 : ℝ) ^ (-2016 : ℝ)) ^ (-(1 / 2016) : ℝ) := by
          rw [← Real.rpow_mul]
          simp
          norm_num
        rw [this]
        apply Real.rpow_lt_rpow_of_neg
        norm_num
        exact h
        norm_num

      -- rewrite (1 - 1 / 100) ^ (-2016) as (1 + 1 / 99) ^ 2016
      have : (1 - 1 / 100 : ℝ) ^ (-2016 : ℝ) = (1 + 1 / 99) ^ 2016 := by norm_num
      rw [this]

      -- then we can apply Bernoulli's inequality, getting
      -- (1 + 1 / 99) ^ 99 ≥ 1 + 99 * (1 / 99) = 2
      have := one_add_mul_le_pow (a := (1 / 99 : ℝ)) (by norm_num) 99
      norm_cast at this
      rw [(by norm_num : 1 + 99 * (1 / 99) = (2 : ℝ))] at this

      -- the rest are routine calculations
      calc
        (1 + 1 / 99 : ℝ) ^ (2016 : ℕ) > (1 + 1 / 99) ^ (99 * 20) := by
          apply pow_lt_pow_right₀ <;> norm_num
        _ = ((1 + 1 / 99) ^ 99) ^ 20 := by ring
        _ ≥ 2 ^ 20 := by
          apply pow_le_pow_left₀
          norm_num
          exact this
        _ > 100 * 2016 := by norm_num
