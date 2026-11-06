import Mathlib

open Real Set

theorem inequalities_221274 (x y z : ℝ) (h : x + y + z = 0) :
    abs (cos x) + abs (cos y) + abs (cos z) ≥ 1 := by
  have h1 : z = -x - y := by linarith
  have h3 : sin z = - (sin x * cos y + cos x * sin y) := by
    rw [h1]
    have h4 : sin (-x - y) = - sin (x + y) := by
      have h5 : -x - y = -(x + y) := by ring
      rw [h5]
      rw [sin_neg]
    have h6 : sin (x + y) = sin x * cos y + cos x * sin y := by
      exact sin_add x y
    rw [h4, h6]
    all_goals ring
  have h2 : cos z = cos x * cos y - sin x * sin y := by
    rw [h1]
    have h3 : cos (-x - y) = cos (x + y) := by
      have h4 : -x - y = -(x + y) := by ring
      rw [h4]
      rw [cos_neg]
    have h4 : cos (x + y) = cos x * cos y - sin x * sin y := by
      exact cos_add x y
    rw [h3, h4]
  have h4 : abs (cos x) + abs (cos y) ≥ abs (sin x) * abs (cos y) + abs (cos x) * abs (sin y) := by
    have h8 : abs (cos x) ≥ 0 := abs_nonneg (cos x)
    have h9 : abs (cos y) ≥ 0 := abs_nonneg (cos y)
    have h10 : abs (sin x) ≥ 0 := abs_nonneg (sin x)
    have h11 : abs (sin y) ≥ 0 := abs_nonneg (sin y)
    have h20 : abs (cos x) + abs (cos y) - (abs (sin x) * abs (cos y) + abs (cos x) * abs (sin y)) ≥ 0 := by
      have h21 : abs (cos x) + abs (cos y) - (abs (sin x) * abs (cos y) + abs (cos x) * abs (sin y)) =
          abs (cos x) * (1 - abs (sin y)) - abs (cos y) * (abs (sin x) - 1) := by
        ring
      rw [h21]
      have h22 : abs (sin x) ≤ 1 := by
        apply abs_le.mpr
        constructor
        · linarith [neg_one_le_sin x]
        · linarith [sin_le_one x]
      have h23 : abs (sin y) ≤ 1 := by
        apply abs_le.mpr
        constructor
        · linarith [neg_one_le_sin y]
        · linarith [sin_le_one y]
      have h24 : 1 - abs (sin y) ≥ 0 := by
        linarith
      have h25 : abs (sin x) - 1 ≤ 0 := by
        linarith
      have h26 : abs (cos x) * (1 - abs (sin y)) ≥ 0 := by
        apply mul_nonneg
        all_goals
          linarith [abs_nonneg (cos x), h24]
      have h27 : abs (cos y) * (abs (sin x) - 1) ≤ 0 := by
        have h28 : abs (cos y) ≥ 0 := abs_nonneg (cos y)
        have h29 : abs (sin x) - 1 ≤ 0 := h25
        nlinarith
      nlinarith
    linarith
  have h5 : abs (sin z) ≤ abs (sin x) * abs (cos y) + abs (cos x) * abs (sin y) := by
    have h10 : sin z = - (sin x * cos y + cos x * sin y) := h3
    rw [h10]
    have h11 : abs (- (sin x * cos y + cos x * sin y)) = abs (sin x * cos y + cos x * sin y) := by
      rw [abs_neg]
    rw [h11]
    have h12 : abs (sin x * cos y + cos x * sin y) ≤ abs (sin x * cos y) + abs (cos x * sin y) := by
      apply abs_add_le
    have h13 : abs (sin x * cos y) = abs (sin x) * abs (cos y) := by
      rw [abs_mul]
    have h14 : abs (cos x * sin y) = abs (cos x) * abs (sin y) := by
      rw [abs_mul]
    have h15 : abs (sin x * cos y) + abs (cos x * sin y) = abs (sin x) * abs (cos y) + abs (cos x) * abs (sin y) := by
      rw [h13, h14]
    linarith [h12, h15]
  have h6 : abs (cos x) + abs (cos y) ≥ abs (sin z) := by
    linarith [h4, h5]
  have h7 : abs (cos z) + abs (sin z) ≥ 1 := by
    cases' abs_cases (cos z) with h1 h1
    ·
      cases' abs_cases (sin z) with h2 h2
      ·
        nlinarith [Real.cos_sq_add_sin_sq z, sq_nonneg (cos z - 1), sq_nonneg (sin z - 0)]
      ·
        nlinarith [Real.cos_sq_add_sin_sq z, sq_nonneg (cos z - 0), sq_nonneg (sin z + 1)]
    ·
      cases' abs_cases (sin z) with h2 h2
      ·
        nlinarith [Real.cos_sq_add_sin_sq z, sq_nonneg (cos z + 1), sq_nonneg (sin z - 0)]
      ·
        nlinarith [Real.cos_sq_add_sin_sq z, sq_nonneg (cos z - 0), sq_nonneg (sin z + 1)]
  have h8 : abs (cos x) + abs (cos y) + abs (cos z) ≥ 1 := by
    linarith [h7, h6]
  exact h8