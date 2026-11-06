import Mathlib

theorem algebra_96906 {xA yA xB yB : ℝ} (hA : 4 * xA^2 + 7 * xA - 1 = yA) (hB : 4 * xB^2 + 7 * xB - 1 = yB)
(hxAB : (xA + xB) / 2 = 0) (hyAB : (yA + yB) / 2 = 0) : Real.sqrt ((xB - xA)^2 + (yB - yA)^2) = 5 * Real.sqrt 2 := by
  -- Show that, if the origin is the midpoint, then the coordinates are opposite sign.
  have hxneg : xA = -xB := by
    field_simp at hxAB
    exact eq_neg_of_add_eq_zero_left hxAB
  have hyneg : yA = -yB := by
    field_simp at hyAB
    exact eq_neg_of_add_eq_zero_left hyAB
  
  -- Substitute and add to get an equation for xB
  rw [hxneg, hyneg] at hA
  simp at hA
  have hxB : (4 * xB ^ 2 + 7 * xB - 1) + (4 * xB ^ 2 + -(7 * xB) - 1) = yB + -yB := by
    rw [hA, hB]
  ring_nf at hxB
  have hxB := Eq.symm <| div_eq_of_eq_mul (by norm_num) <| add_eq_of_eq_neg_add (Eq.symm hxB)
  norm_num at hxB

  -- xB is either the positive or negative square root
  by_cases hxpos : xB >= 0
  · have hxBval := Eq.symm <| Real.sqrt_eq_iff_eq_sq (by norm_num) (by exact hxpos) |>.mpr (Eq.symm hxB)
    -- Substitute xB in other coordinate values
    rw [hxBval] at hxneg
    rw [hxBval] at hB
    norm_num at hB
    rw [←hB] at hyneg
    rw [hxBval, hxneg, hyneg, ←hB]
    -- Simplify and solve for distance
    field_simp
    norm_num
    rw [←@Real.sqrt_sq 5 (by norm_num)]
    rw [←Real.sqrt_mul (by norm_num), ←Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_inj (by norm_num) (by norm_num) |>.mpr
    norm_num
  · rw [←neg_sq] at hxB
    apply lt_iff_not_ge xB 0 |>.mpr at hxpos
    have hxnneg : 0 ≤ -xB := by
      field_simp
      linarith
    have hxBval := Eq.symm <| Real.sqrt_eq_iff_eq_sq (by norm_num) hxnneg |>.mpr (Eq.symm hxB)
    -- Substitute xB in other coordinate values
    apply neg_eq_iff_eq_neg.mp at hxBval
    rw [hxBval] at hxneg
    rw [hxBval] at hB
    norm_num at hB
    rw [←hB] at hyneg
    rw [hxBval, hxneg, hyneg, ←hB]
    -- Simplify and solve for distance
    norm_num
    field_simp
    norm_num
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
    rw [←@Real.sqrt_sq 20 (by norm_num), ←Real.sqrt_mul (by norm_num), ←Real.sqrt_mul (by norm_num)]
    norm_num