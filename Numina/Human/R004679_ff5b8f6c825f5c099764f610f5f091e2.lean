import Mathlib

open Real
/--
Problem statement (Main theorem of this file):
2. If the equation $\lg (k x)=2 \lg (x+1)$ has only one real solution, then the range of values for $k$ is $\qquad$ .

Solution:
2. The original equation is equivalent to $$ \left\{\begin{array}{l} k x > 0 \\ x+1 > 0 \\ k x=(x+1)^{2} \end{array}\right. $$ $y_{1}=k x( > 0)$ is the part of the line above the $x$-axis, $y_{2}=$ $(x+1)^{2}$ is a parabola with its vertex at $(-1, 0)$ and opening upwards.

Thus, the problem is converted to finding the range of $k$ such that $y_{1}$ and $y_{2}$ have only one intersection point when $x > -1$. As shown in the figure, when $y_{1}$ is tangent to $y_{2}$, $k=4$ or $k < 0$, the two curves have only one intersection point. Therefore, the range of $k$ is $$ k=4 \text { or } k < 0 \text {. } $$

-/
theorem algebra_299301  {k : ℝ} :
  (∃! x : ℝ, k * x > 0 ∧ x > -1 ∧ logb 10 (k * x) = 2 * logb 10 (x + 1))
    ↔ (k = 4 ∨ k < 0) := by

  constructor
  . intro hx
    rcases hx with ⟨x, ⟨hx1, hx2, hx3⟩, hy⟩
    rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
    apply logb_injOn_pos (by linarith) (by simp; linarith) (by simp; nlinarith) at hx3
    norm_cast at hx3
    by_contra hk1
    simp at hk1
    by_cases hk3 : k > 4
    . let x1 := -1 + k/2 + sqrt (k^2 -4*k)/2
      let x2 := -1 + k/2 - sqrt (k^2 -4*k)/2

      have hx11 : k * x1 > 0 := by
        have : sqrt (k^2 -4*k)/2 ≥ 0 := by positivity
        unfold x1
        nlinarith

      have hx12 : x1 > -1 := by nlinarith
      have hx13 : logb 10 (k * x1) = 2 * logb 10 (x1 + 1) := by
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
        suffices k * x1 = (x1 + 1) ^ 2 by rw [this]; simp
        unfold x1
        ring_nf
        field_simp
        rw [sq_sqrt (by nlinarith)]
        ring_nf

      have hx21 : k*x2 > 0 := by
        unfold x2
        suffices -2 + k > √(k ^ 2 - 4 * k) by nlinarith
        apply lt_of_mul_self_lt_mul_self₀ (by linarith)
        rw [← pow_two, sq_sqrt (by nlinarith)]
        ring_nf
        field_simp
      have hx22 : x2 > -1 := by nlinarith
      have hx23 : logb 10 (k * x2) = 2 * logb 10 (x2 + 1) := by
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
        suffices k * x2 = (x2 + 1) ^ 2 by rw [this]; simp
        unfold x2
        ring_nf
        field_simp
        rw [sq_sqrt (by nlinarith)]
        ring_nf

      have hy1 := hy x1; simp at hy1
      have hy1 := hy1 hx11 hx12 hx13
      have hy2 := hy x2; simp at hy2
      have hy2 := hy2 hx21 hx22 hx23

      rw [← hy1] at hy2
      unfold x1 x2 at hy2
      have : √(k ^ 2 - 4 * k) = 0 := by linarith
      rw [sqrt_eq_zero (by nlinarith)] at this
      nlinarith

    . by_cases hk4 : k = 0
      . rw [hk4] at hx1; simp at hx1
      . have hk5: 0 < k := lt_of_le_of_ne hk1.2 (Ne.symm hk4)
        simp at hk3
        have hk6: k < 4 := lt_of_le_of_ne hk3 hk1.1
        have : (x + (2 - k)/2) ^ 2 ≥ 0 := by positivity
        nlinarith

  . intro hk
    rcases hk with rfl | hk
    . use 1
      constructor
      . simp
        rw [← logb_rpow_eq_mul_logb_of_pos (by norm_num)]
        norm_num
      . intro x ⟨hx1, hx2, hx3⟩
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
        apply logb_injOn_pos (by linarith) (by simp; linarith) (by simp; nlinarith) at hx3
        norm_cast at hx3
        have : (x-1)^2 = 0 := by linarith
        simp at this
        linarith

    . use -1 + k/2 + sqrt (k^2 -4*k)/2
      constructor
      . simp
        constructor
        . have : (-1 + k / 2 + √(k ^ 2 - 4 * k) / 2) < 0 := by
            suffices √(k ^ 2 - 4 * k) < 2 - k by linarith
            apply lt_of_mul_self_lt_mul_self₀ (by linarith)
            rw [← pow_two, sq_sqrt (by nlinarith)]
            ring_nf
            field_simp
          nlinarith
        . have hk1: 0 ≤ k ^ 2 - 4 * k := by nlinarith
          have hk2: -k < √(k ^ 2 - 4 * k) := by
            apply lt_of_mul_self_lt_mul_self₀ (by positivity)
            rw [← pow_two, ← pow_two, sq_sqrt hk1]
            field_simp
            linarith

          constructor
          . linarith
          . have : 0 < -1 + k / 2 + √(k ^ 2 - 4 * k) / 2 + 1 := by linarith
            rw [← logb_rpow_eq_mul_logb_of_pos this]
            have : k * (-1 + k / 2 + √(k ^ 2 - 4 * k) / 2) = (-1 + k / 2 + √(k ^ 2 - 4 * k) / 2 + 1) ^ 2 := by
              ring_nf
              rw [sq_sqrt (by linarith)]
              field_simp
              ring_nf
            rw [this]; simp

      . intro x ⟨hx1, hx2, hx3⟩
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
        apply logb_injOn_pos (by linarith) (by simp; linarith) (by simp; nlinarith) at hx3
        norm_cast at hx3
        have : (x - (-1 + k/2 + sqrt (k^2 -4*k)/2)) * (x - (-1 + k/2 - sqrt (k^2 -4*k)/2)) = 0 := by
          ring_nf
          rw [sq_sqrt (by nlinarith)]
          nlinarith

        simp at this
        rcases this with h1 | h2
        . linarith
        . have : x = (-1 + k / 2 - √(k ^ 2 - 4 * k) / 2) := by linarith
          rw [this] at hx2
          have : √(k ^ 2 - 4 * k) ≥ 0 := by positivity
          linarith
