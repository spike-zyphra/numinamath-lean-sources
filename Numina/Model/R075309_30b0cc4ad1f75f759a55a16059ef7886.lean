import Mathlib

theorem algebra_15412 (A B C D E : Real)
    (h₀ : A > 0) (h₁ : B > 0) (h₂ : C > 0) (h₃ : D > 0) (h₄ : E > 0)
    (h₅ : A + B + C + D + E = 540) (h₆ : A / B = 3 / 3) (h₇ : B / C = 3 / 3)
    (h₈ : C / D = 3 / 4) (h₉ : D / E = 4 / 5) :
    max (max (max (max A B) C) D) E = 150 := by
  have h10 : A = B := by
    have h₆' : B ≠ 0 := by linarith
    field_simp [h₆'] at h₆
    linarith
  have h11 : B = C := by
    have h₇' : C ≠ 0 := by linarith
    field_simp [h₇'] at h₇
    linarith
  -- D in terms of C
  have h12 : 4 * C = 3 * D := by
    have h₈' : D ≠ 0 := by linarith
    field_simp [h₈'] at h₈
    linarith
  have h12' : D = (4 / 3) * C := by
    linarith
  -- E in terms of D
  have h13 : 5 * D = 4 * E := by
    have h₉' : E ≠ 0 := by linarith
    field_simp [h₉'] at h₉
    linarith
  have h13' : E = (5 / 4) * D := by
    linarith
  rw [h12'] at h13' 
  have hE : E = (5 / 3) * C := by
    linarith
  -- Express all variables in terms of C
  have hA : A = C := by
    linarith [h10, h11]
  have hB : B = C := by 
    linarith [h11]
  -- substitution into sum equation
  have hSum : A + B + C + D + E = 540 := h₅
  rw [show A = C by linarith [hA], 
        show B = C by linarith [hB], 
        show D = (4 / 3) * C by linarith [h12'], 
        show E = (5 / 3) * C by linarith [hE]
      ] at hSum 
  have hC : C = 90 := by
    linarith
  -- Now solving to get all angles
  have hA' : A = 90 := by
    linarith [show A = C by linarith [hA], hC]
  have hB' : B = 90 := by
    linarith [show B = C by linarith [hB], hC]
  have hD' : D = 120 := by
    rw [show C = 90 by linarith [hC]] at h12'
    linarith
  have hE' : E = 150 := by
    rw [show C = 90 by linarith [hC]] at hE
    linarith
  -- Now we can compute the max
  rw [show A = 90 by linarith [hA'], 
    show B = 90 by linarith [hB'], 
    show C = 90 by linarith [hC], 
    show D = 120 by linarith [hD'], 
    show E = 150 by linarith [hE']
    ]
  norm_num [max_eq_right, max_eq_left]
  all_goals norm_num
  <;> try { tauto }