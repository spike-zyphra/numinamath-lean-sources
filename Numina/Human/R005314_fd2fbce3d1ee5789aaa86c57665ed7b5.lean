import Mathlib

/- Calculer

$$
\sqrt{1+\frac{1}{1^{2}}+\frac{1}{2^{2}}}+\sqrt{1+\frac{1}{2^{2}}+\frac{1}{3^{2}}}+\cdots+\sqrt{1+\frac{1}{2014^{2}}+\frac{1}{2015^{2}}}
$$ -/
theorem algebra_607592 : ∑ i ∈ Finset.range 2014, Real.sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = 2015 - 1 / 2015 := by
  -- transform the item in the sqrt into squares
  have (i:ℕ): 1 + 1 / ((i:ℝ) + 1)^2 + 1 / (i + 2) ^ 2 = (1 + (1 / (i + 1) - 1 / (i + 2))) ^ 2 :=
    calc
      _ = 1 + ((i:ℝ) + 2)^2 / (i + 2)^2 / (i + 1)^2 + (i + 1)^2/ (i + 1)^2 / (i + 2)^2 := by
        rw [div_self, div_self]
        all_goals {simp; norm_cast}
      _ = ((i + 1)^2 * (i + 2)^2) / ((i + 1)^2 * (i + 2)^2) + (i + 2)^2 / (i + 2)^2 / (i + 1)^2 + (i + 1)^2/ (i + 1)^2 / (i + 2)^2 := by
        nth_rw 3 [div_self]
        simp
        norm_cast
      _ = ((i + 1)^2 * (i + 2)^2) / ((i + 1)^2 * (i + 2)^2) + (i + 2)^2 / ((i + 1)^2 * (i + 2)^2) + (i + 1)^2/ ((i + 1)^2 * (i + 2)^2) := by
        rw [div_div, div_div]
        nth_rw 3 [mul_comm]
      _ = ((i + 1)^2 + (i + 2))^2 / ((i + 1) * (i + 2))^2 := by ring
      _ = (((i + 1)^2 + (i + 2)) / ((i + 1) * (i + 2))) ^ 2 := by rw [div_pow]
      _ = ((((i + 1) * (i + 2)) + (i + 2) - (i + 1)) / ((i + 1) * (i + 2))) ^ 2 := by ring
      _ = ((i + 1) * (i + 2)/ ((i + 1) * (i + 2)) + (i + 2) / ((i + 1) * (i + 2)) - (i + 1) / ((i + 1) * (i + 2)) ) ^ 2 := by ring
      _ = (1 + 1 / (i + 1)  - 1 / (i + 2)) ^ 2 := by
        rw [div_self, <-div_div, <-div_div, div_right_comm, div_self, div_self]
        all_goals {simp; norm_cast}
      _ = (1 + (1 / (i + 1) - 1 / (i + 2))) ^ 2 := by ring_nf
  -- cancel the square root
  -- transform the goal into $\sum_{x=0}^{2014} 1 + \sum_{x=0}^{2014} (1 / (↑x + 1) - 1 / (↑x + 2)))$
  replace : ∀ i ∈ Finset.range 2014, Real.sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = 1 + (1 / (i + 1) - 1 / (i + 2)) := by
    intro i _
    rw [this i]
    apply Real.sqrt_sq
    apply add_nonneg
    norm_cast
    simp
    rw [inv_le_inv₀]
    simp
    all_goals linarith
  rw [
    Finset.sum_congr rfl this,
    Finset.sum_add_distrib,
    -- calculate $\sum_{x=0}^{2014} 1$
    Finset.sum_eq_card_nsmul (show ∀ i ∈ Finset.range 2014, (1:ℝ) = 1 by intros; rfl),
    Finset.card_range,
    nsmul_eq_mul,
    mul_one,
    Nat.cast_ofNat
  ]
  -- using induction to calculate $\sum_{x=0}^{2014} (1 / (↑x + 1) - 1 / (↑x + 2))$
  have (n: ℕ): ∑ x ∈ Finset.range n, (1 / ((x:ℝ) + 1) - 1 / (↑x + 2)) = 1 - 1 / (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp
      ring
  rw [this]
  -- simplify the goal
  rw [Nat.cast_ofNat, add_sub, show 2014 + 1 = (2015:ℝ) by norm_num]
