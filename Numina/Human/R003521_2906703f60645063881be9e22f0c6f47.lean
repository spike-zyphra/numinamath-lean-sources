import Mathlib

open Real

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem algebra_190577 {S : Finset ℤ}
  (hS : ↑S = {k : ℤ | k ∈ Finset.Icc (-500) 500 ∧ ∃! x : ℝ, 0 < k * x ∧ x > -2 ∧ logb 10 (k * x) = 2 * logb 10 (x + 2)})
  : S.card = 501 := by

  let S1 := Finset.Icc (-500) (-1)

  have hS1 : S1.card = 500 := by
    native_decide

  suffices S = S1 ∪ {8} by
    rw [this]
    rw [Finset.card_union_of_disjoint]
    rw [hS1]
    all_goals simp
    native_decide

  ext k
  unfold S1
  rw [Finset.mem_union, Finset.mem_singleton]
  -- 使用 Finset.mem_coe 来连接 Finset 和 Set 的成员关系
  rw [← Finset.mem_coe]
  rw [hS]
  simp only [Set.mem_setOf_eq, Finset.mem_Icc]


  let x1 := k / 2 - 2 - √(k ^ 2 - 8 * k)/2
  let x2 := k / 2 - 2 + √(k ^ 2 - 8 * k)/2
  constructor
  . intro ⟨⟨hk1, hk2⟩, ⟨x, ⟨hx, hy⟩⟩⟩
    simp at hx
    have ⟨hx1, hx2, hx3⟩ := hx
    rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
    have : x + 2 > 0 := by linarith
    apply logb_injOn_pos (by norm_num) (by simp; linarith) (by simp; positivity) at hx3
    by_contra hk1
    simp at hk1
    have ⟨hk1, hk2⟩ := hk1
    have hk0 : k ≠ 0 := by
      by_contra h
      rw [h] at hx1
      norm_cast at hx1
      linarith

    have hk3 : k > (0:ℝ) := by
      norm_cast
      omega

    have hk4 : k > 7 := by
      by_contra h
      simp at h
      norm_cast at hx3
      ring_nf at hx3
      have : (x+2-k/2)^2 ≥ 0 := by positivity
      ring_nf at this
      rw [show x^2 = k*x-4-4*x by linarith] at this
      ring_nf at this
      field_simp at this
      rw [div_nonneg_iff] at this
      norm_num at this
      norm_cast at this
      have : k * (8-k) ≤ 0 := by linarith
      norm_cast at hk3
      nlinarith

    have hk5 : k > 8 := by
      omega

    have hy1 := hy x1
    have hy2 := hy x2
    simp at hy1 hy2

    have : x1 > 0 := by
      unfold x1
      suffices √(k ^ 2 - 8 * k) < k - 4 by
        linarith

      rw [sqrt_lt]
      all_goals norm_cast; nlinarith


    have : x2 > 0 := by
      unfold x2
      suffices 4 - k <√(k ^ 2 - 8 * k) by
        linarith

      have : √(k ^ 2 - 8 * k) ≥ 0 := by positivity
      have : 4-k < (0:ℝ) := by norm_cast; linarith
      linarith

    have hx1eq : logb 10 (k * x1) = 2 * logb 10 (x1 + 2) := by
      rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
      suffices k * x1 = (x1 + 2) ^ 2 by
        rw [this]
        norm_cast
      unfold x1
      ring_nf
      rw [sq_sqrt]
      . ring_nf
      . norm_cast
        nlinarith

    have hx2eq : logb 10 (k * x2) = 2 * logb 10 (x2 + 2) := by
      rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
      suffices k * x2 = (x2 + 2) ^ 2 by
        rw [this]
        norm_cast
      unfold x2
      ring_nf
      rw [sq_sqrt]
      . ring_nf
      . norm_cast
        nlinarith

    have hy1 := hy1 (by nlinarith) (by linarith) hx1eq
    have hy2 := hy2 (by nlinarith) (by linarith) hx2eq

    rw [← hy2] at hy1
    unfold x1 x2 at hy1
    have : √(↑k ^ 2 - 8 * ↑k) = 0 := by
      linarith

    rw [sqrt_eq_zero'] at this
    norm_cast at this
    nlinarith


  . intro hx
    rcases hx with ⟨hk1, hk2⟩ | rfl
    . refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      use x2
      constructor
      . simp

        have hx2: -2 < x2 := by
          unfold x2
          suffices -k < √(k ^ 2 - 8 * k) by
            linarith

          rw [lt_sqrt]
          all_goals norm_cast; nlinarith

        have hx2neg : x2 < 0 := by
          unfold x2
          suffices √(k ^ 2 - 8 * k) < 4-k by
            linarith

          rw [sqrt_lt]
          all_goals norm_cast; nlinarith

        refine ⟨?_, hx2, ?_⟩
        . have : k < (0:ℝ) := by norm_cast; linarith
          nlinarith
        . rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
          suffices k * x2 = (x2 + 2) ^ 2 by
            rw [this]
            norm_cast
          unfold x2
          ring_nf
          rw [sq_sqrt]
          . ring_nf
          . norm_cast
            nlinarith
      . intro x ⟨hx1, hx2, hx3⟩
        have : k < 0 := by linarith

        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
        have : x + 2 > 0 := by linarith
        apply logb_injOn_pos (by norm_num) (by simp; linarith) (by simp; positivity) at hx3
        norm_cast at hx3
        ring_nf at hx3

        have : (x-x1) * (x-x2) = 0 := by
          ring_nf
          rw [sq_sqrt]
          . ring_nf
            nth_rw 2 [mul_comm]
            rw [hx3]
            ring_nf
          . norm_cast
            nlinarith

        simp at this
        rcases this with h1 | h2

        . have : x = x1 := by linarith
          rw [this] at hx2
          unfold x1 at hx2
          have : √(k ^ 2 - 8 * k) ≥ 0 := by positivity
          have : k < (0:ℝ) := by norm_cast
          linarith
        . linarith

    . norm_num
      use 2
      constructor
      . simp
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
        norm_num

      . intro x ⟨hx1, hx2, hx3⟩
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
        apply logb_injOn_pos (by norm_num) (by simp; linarith) (by simp; positivity) at hx3

        norm_cast at hx3
        ring_nf at hx3
        have : (x-2)^2 = 0 := by
          nlinarith

        simp at this
        linarith
