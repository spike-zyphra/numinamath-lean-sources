import Mathlib

open Real

/- Compute \[ \frac {\sum_{n = 1}^{44} \cos n^\circ}{\sum_{n = 1}^{44} \sin n^\circ} .\] -/
theorem calculus_22708 : (∑ n in Finset.range 44, cos ((n + 1) * (π / 180))) / (∑ n in Finset.range 44, sin ((n + 1) * (π / 180))) = 1 + √2 := by
  -- $A = \sum_{n = 1}^{44} \cos n^\circ$ and $B = \sum_{n = 1}^{44} \sin n^\circ.$
  let A := ∑ n in Finset.range 44, cos ((n + 1) * (π / 180))
  let B := ∑ n in Finset.range 44, sin ((n + 1) * (π / 180))
  -- $A + B = A \sqrt{2}.$
  have hA : A + B = A * Real.sqrt 2 := by
    -- $\cos (45^\circ - n^\circ) = \cos 45^\circ \cos n^\circ + \sin 45^\circ \sin n^\circ = \frac{1}{\sqrt{2}} \cos n^\circ + \frac{1}{\sqrt{2}} \sin n^\circ,$
    have h : ∀ n ∈ Finset.range 44, cos ((n + 1) * (π / 180)) + sin ((n + 1) * (π / 180)) = Real.sqrt 2 * cos (45 * (π / 180) - (n + 1) * (π / 180)) := by
      intro n _
      rw [cos_sub]
      have mid : 45 * (π / 180) = π / 4 := by
        calc
          45 * (π / 180) = 45 * π / 180 := by ring
          _ = π * (45 / 180) := by ring
          _ = _ := by 
            norm_num
            exact Eq.symm (div_eq_mul_one_div π 4)
      rw [mid, cos_pi_div_four, sin_pi_div_four]
      rw [mul_add, ← mul_assoc, ← mul_assoc]
      have mid2 : √2 * (√2 / 2) = 1 := by
        rw [mul_div, ← pow_two, sq_sqrt]
        exact div_self_of_invertible 2
        exact zero_le_two
      rw [mid2]
      ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl h, ← Finset.sum_flip, Finset.sum_mul]
    apply Finset.sum_congr
    exact rfl
    -- $\forall n \in \{1, 2, \dots, 44\}, \sqrt{2} \cos (45^\circ - (43 - n + 1)^\circ) = \cos (n + 1)^\circ.$
    intro n hn
    rw [Finset.mem_range] at hn
    rw [mul_comm, ← sub_mul]
    have mid : ((43 - n : ℕ) : ℝ) = 43 - n := by
      refine eq_sub_of_add_eq' ?_
      rw [← Nat.cast_add, add_comm n, Nat.sub_add_cancel (by linarith)]
      simp only [Nat.cast_ofNat]
    rw [mid]
    ring_nf
  -- $B = A (\sqrt{2} - 1).$
  have hB : B = A * (Real.sqrt 2 - 1) := by
    linarith
  -- $\frac{A}{B} = \frac{A}{A (\sqrt{2} - 1)} = 1 + \sqrt{2}.$
  have hAB : A / B = 1 + Real.sqrt 2 := by
    rw [hB]
    -- $A > 0.$
    have hApos : A > 0 := by
      have ltpi : 0 < π := by
        exact pi_pos
      dsimp [A]
      -- $\forall n \in \{1, 2, \dots, 44\}, \cos n^\circ > 0.$
      apply Finset.sum_pos
      intro n hn
      rw [Finset.mem_range] at hn
      -- $(n + 1) * \frac{\pi}{180} \in (-\frac{\pi}{2}, \frac{\pi}{2}).$
      apply cos_pos_of_mem_Ioo
      constructor
      have le3 : 0 < (↑n + 1) * (π / 180) := by
        apply mul_pos
        linarith
        linarith
      linarith
      have le : (↑n + 1) * (π / 180) * 180 < π / 2 * 180 := by
        have nlt : (n : ℝ) < 44 := by
          exact Nat.cast_lt_ofNat.mpr hn
        field_simp
        rw [← mul_div, mul_comm]
        have le2 : (n : ℝ) + 1 < 180 / 2 := by
          norm_num
          linarith
        exact (mul_lt_mul_left ltpi).mpr le2
      linarith
      exact Finset.nonempty_range_succ
    -- $A * (\sqrt{2} - 1) \neq 0.$
    have hAne : (A * (√2 - 1)) ≠ 0 := by
      apply mul_ne_zero
      exact Ne.symm (ne_of_lt hApos)
      apply sub_ne_zero_of_ne
      by_contra contra
      apply congrArg (fun x ↦ x ^ 2) at contra
      rw [sq_sqrt, one_pow] at contra
      linarith
      linarith
    field_simp [hAne]
    ring_nf
    rw [sq_sqrt (by linarith)]
    ring
  simp only [A, B] at hAB
  exact hAB