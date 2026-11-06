import Mathlib
open Real

theorem algebra_218015 (a : ℝ) :
  (∃! x : ℝ, x > -3 ∧ a * x > 0 ∧ 2 * logb 10 (x + 3) = logb 10 (a * x)) ↔ (a < 0 ∨ a = 12) := by
  constructor
  . intro hx
    rcases hx with ⟨x, ⟨⟨hx1, hx2, hx3⟩, hy⟩⟩
    rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
    apply logb_injOn_pos (by norm_num) (by simp; nlinarith) (by simp; linarith) at hx3
    norm_cast at hx3

    by_cases ha1: a > 12
    . let x1 := -3+a/2 - sqrt ((a-12)*a)/2
      let x2 := -3+a/2 + sqrt ((a-12)*a)/2

      have hx1_1 : -3 < x1 := by
        unfold x1
        suffices √((a - 12) * a) < a by
          linarith

        rw [sqrt_lt' (by linarith)]
        nlinarith

      have hx1_2 : 0 < a * x1 := by
        suffices x1 > 0 by nlinarith
        unfold x1
        suffices √((a - 12) * a) < a - 6 by
          linarith

        rw [sqrt_lt' (by linarith)]
        nlinarith

      have hx1_3 : 2 * logb 10 (x1 + 3) = logb 10 (a * x1) := by
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
        suffices (x1 + 3) ^ 2 = a * x1 by
          rw [← this]
          norm_cast

        unfold x1
        ring_nf
        field_simp
        rw [sq_sqrt (by nlinarith)]
        ring_nf

      have hx2_1 : -3 < x2 := by
        unfold x2
        have : √((a - 12) * a) ≥ 0 := by positivity
        linarith

      have hx2_2 : 0 < a * x2 := by
        suffices x2 > 0 by nlinarith
        unfold x2
        suffices 6 - a < √((a - 12) * a) by
          linarith

        have : √((a - 12) * a) ≥ 0 := by positivity
        linarith

      have hx2_3 : 2 * logb 10 (x2 + 3) = logb 10 (a * x2) := by
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
        suffices (x2 + 3) ^ 2 = a * x2 by
          rw [← this]
          norm_cast

        unfold x2
        ring_nf
        field_simp
        rw [sq_sqrt (by nlinarith)]
        ring_nf

      have hy1 := hy x1
      have hy2 := hy x2

      simp at hy1 hy2

      have hy1 := hy x1 ⟨hx1_1, hx1_2, hx1_3⟩
      have hy2 := hy x2 ⟨hx2_1, hx2_2, hx2_3⟩

      rw [← hy2] at hy1
      unfold x1 x2 at hy1
      have : √((a - 12) * a) = 0 := by linarith
      rw [sqrt_eq_zero (by nlinarith)] at this

      nlinarith
    . by_cases ha2: a = 12
      . right; assumption
      . simp at ha1
        have ha3: a < 12 := lt_of_le_of_ne ha1 ha2
        by_cases ha4: a > 0
        . have : x^2 = (a-6) * x- 9 := by linarith
          have : (x+3-a/2)^2=(a-12)*a/4 := by
            ring_nf
            rw [this]
            linarith

          have : (a-12)*a/4 ≥ 0 := by
            rw [← this]
            positivity

          nlinarith
        . by_cases ha5: a = 0
          . subst a
            simp at hx2
          . simp at ha4
            have ha6: a < 0 := lt_of_le_of_ne ha4 ha5
            left; assumption

  . intro ha
    rcases ha with ha1 | rfl
    . use -3+a/2 + sqrt ((a-12)*a)/2
      constructor
      . simp
        have : -a <  √((a - 12) * a) := by
          rw [lt_sqrt (by linarith)]
          nlinarith

        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]

        constructor
        . suffices -a < √((a - 12) * a) by linarith

          rw [lt_sqrt (by linarith)]
          nlinarith

        . constructor
          . suffices √((a - 12) * a) < 6 - a by nlinarith
            rw [sqrt_lt' (by linarith)]
            nlinarith

          . suffices (-3 + a / 2 + √((a - 12) * a) / 2 + 3) ^ 2 = a * (-3 + a / 2 + √((a - 12) * a) / 2) by
              rw [← this]
              norm_cast
            ring_nf
            field_simp
            rw [sq_sqrt (by nlinarith)]
            ring_nf

      . intro x ⟨hx1, hx2, hx3⟩
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
        apply logb_injOn_pos (by norm_num) (by simp; nlinarith) (by simp; linarith) at hx3
        norm_cast at hx3
        have : (x - (-3+a/2+sqrt ((a-12)*a)/2)) * (x - (-3+a/2-sqrt ((a-12)*a)/2)) = 0 := by
          ring_nf
          field_simp
          rw [sq_sqrt (by nlinarith)]
          ring_nf
          linarith

        simp at this
        rcases this with h1 | h2
        . linarith
        . have : x = (-3 + a / 2 - √((a - 12) * a) / 2) := by linarith
          rw [this] at hx1
          have : √((a - 12) * a) < a := by linarith
          have : √((a - 12) * a) ≥ 0 := by positivity
          linarith

    . use 3
      constructor
      . simp
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)]
        norm_num

      . intro x ⟨hx1, hx2, hx3⟩
        rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at hx3
        apply logb_injOn_pos (by norm_num) (by simp; nlinarith) (by simp; linarith) at hx3
        norm_cast at hx3
        have : (x - 3) ^ 2 = 0 := by linarith
        simp at this
        linarith
