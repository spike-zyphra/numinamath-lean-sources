import Mathlib

/- Soient $k, m, n>0$ des entiers tels que $m^{2}+n=k^{2}+k$. Montrer que $m \leqslant n$. -/
theorem number_theory_607434 (k m n : ℤ) (h₀ : 0 < k) (h₁ : 0 < m) (h₂ : 0 < n)
    (h₃ : m^2 + n = k^2 + k) : m ≤ n := by

      -- Note that (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 = 4 * (m ^ 2 + n) + 1 = 4 * m ^ 2 + 4 * n + 1.
  have claim1 : (2 * k + 1) ^ 2 = 4 * m ^ 2 + 4 * n + 1 := by
    calc
     _ = 4 * (k ^ 2 + k) + 1 := by ring
     _ = 4 * (m ^ 2 + n) + 1 := by rw [h₃]
     _ = _ := by ring

  -- Since n > 0, we have 4 * m ^ 2 + n + 1 > 4 * m ^ 2 = (2 * m) ^ 2.
  have claim2 : 4 * m ^ 2 + n + 1 > (2 * m) ^ 2 := by
    calc
     _ = 4 * m ^ 2 + (n + 1) := by rw [add_assoc]
     _ > 4 * m ^ 2 + 0:= by have : n + 1 > 0 := by linarith
                            exact Int.add_lt_add_left this (4 * m ^ 2)
     _ = (2 * m) ^ 2 := by ring

  -- Hence, (2 * k + 1) ^ 2 > (2 * m) ^ 2.
  have claim3 : (2 * k + 1) ^ 2 > (2 * m) ^ 2 := by omega

  rw [gt_iff_lt, sq_lt_sq] at claim3

  -- It follows that 2 * k + 1 > 2 * m as 2 * k + 1 > 0 and 2 * m > 0
  -- since k > 0 and m > 0 by assumption.
  -- As 2 * k + 1 and 2 * m are integers, we have 2 * k + 1 ≥ 2 * m + 1
  have claim4 : 2 * k + 1 ≥ 2 * m + 1:= by
    have : |2 * m| = 2 * m := by rw [abs_eq_self]; omega
    rw [this] at claim3
    have : |2 * k + 1| = 2 * k + 1 := by rw [abs_eq_self]; omega
    rw [this] at claim3
    exact claim3

  -- It follows that (2 * k + 1) ^ 2 ≥ (2 * m + 1) ^ 2 as
  -- as 2 * k + 1 > 0 and 2 * m > 0 since k > 0 and m > 0 by assumption.
  have claim5 : (2 * k + 1) ^ 2 ≥ (2 * m + 1) ^ 2 := by
    suffices |2 * k + 1| ≥ |2 * m + 1| by exact sq_le_sq.mpr this
    have : |2 * m + 1| = 2 * m + 1 := by rw [abs_eq_self]; omega
    rw [this]
    have : |2 * k + 1| = 2 * k + 1 := by rw [abs_eq_self]; omega
    rw [this]
    exact claim4

  -- Since (2 * k + 1) ^ 2 = 1 + 4 * m ^ 2 + 4 * n and
  -- (2 * m + 1) ^ 2 = 1 + 4 * m ^ 2 + 4 * m, we have
  -- 1 + 4 * m ^ 2 + 4 * n ≥ 1 + 4 * m ^ 2 + 4 * m.
  have claim6 : 1 + 4 * m ^ 2 + 4 * n ≥ 1 + 4 * m ^ 2 + 4 * m := by
    calc
      _ = 4 * (m ^ 2 + n) + 1 := by ring
      _ = 4 * (k ^ 2 + k) + 1 := by rw [h₃]
      _ = (2 * k + 1) ^ 2 := by ring
      _ ≥ (2 * m + 1) ^ 2 := by exact claim5
      _ = _ := by ring

  -- It follows that 4 * n ≥ 4 * m.
  have claim7 : 4 * n ≥ 4 * m := by exact (Int.add_le_add_iff_left (1 + 4 * m ^ 2)).mp claim6

  -- As 4 is positive, we obtain that n ≥ m, as desired.
  apply Int.le_of_mul_le_mul_left
  . exact claim7
  . norm_num
