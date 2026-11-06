import Mathlib

theorem Inequalities_147869 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hd : d > 0) :
  a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) ≥ 4 / 3 
  := by 
  let A := b + c + d
  let B := a + c + d
  let C := a + b + d
  let D := a + b + c
  let E := a + b + c + d
  have eq1 : a / A + b / B + c / C + d / D = 
  E * (1 / A + 1 / B + 1 / C + 1 / D) - 4 := by 
    calc 
      _ = (a + A) / A + (b + B) / B + (c + C) / C + (d + D) / D - 4:= by 
        field_simp; ring_nf
      _ = E / A + E / B + E / C + E / D - 4:= by 
        simp
        have aeq : a + A = E := by unfold A; unfold E; linarith
        have beq : b + B = E := by unfold B; unfold E; linarith
        have ceq : c + C = E := by unfold C; unfold E; linarith
        have deq : d + D = E := by unfold D; unfold E; linarith
        rw [aeq, beq, ceq, deq]
      _ = _ := by 
        field_simp
        ring
  have eq2 : 3 * E = A + B + C + D := by ring
  have ineq_aux (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0): 
    x + y  ≥ 2 * (x * y) ^ ((1:ℝ) / 2) := by
      have aux1 : x + y = |x + y| := by 
        unfold abs
        simp
        linarith
      have aux2 : 2 * (x * y) ^ ((1:ℝ) / 2) = |2 * (x * y) ^ ((1:ℝ) / 2)| := by 
        unfold abs
        simp
        positivity
      rw [aux1, aux2]
      refine sq_le_sq.mp ?_
      have aux3 : (2 * (x * y) ^ (1 / (2 : ℝ))) ^ 2 = 4 * x * y := by
        ring_nf
        congr
        have aux4 : ((x * y) ^ (1 / (2 : ℝ))) ^ (2 : ℕ)
          = ((x * y) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by norm_cast
        rw [aux4, ←Real.rpow_mul (by positivity) (1 / (2 : ℝ)) 2 (x := x * y)]
        simp
      rw [aux3]
      nlinarith [sq_nonneg (x - y)]
  have eq3 : (A + B + C + D) * (1 / A) = A / A + B / A + C / A + D / A := by 
    ring
  have eq4 : (A + B + C + D) * (1 / B) = A / B + B / B + C / B + D / B := by
    ring
  have eq5 : (A + B + C + D) * (1 / C) = A / C + B / C + C / C + D / C := by
    ring
  have eq6 : (A + B + C + D) * (1 / D) = A / D + B / D + C / D + D / D := by
    ring
  
  have ineq1 : (A + B + C + D) * (1 / A + 1 /B + 1 / C + 1 / D) ≥ 16 := by 
    have ineq1 : B / A + A / B ≥ 2 := by
      obtain h' := ineq_aux (B / A) (A / B) (by positivity) (by positivity)
      simp at h'
      field_simp at h'
      field_simp
      exact h'
    have ineq2 : C / B + B / C ≥ 2 := by
      obtain h' := ineq_aux (C / B) (B / C) (by positivity) (by positivity)
      simp at h'
      field_simp at h'
      field_simp
      exact h'
    have ineq3 : D / C + C / D ≥ 2 := by
      obtain h' := ineq_aux (D / C) (C / D) (by positivity) (by positivity)
      simp at h'
      field_simp at h'
      field_simp
      exact h'
    have ineq4 : A / D + D / A ≥ 2 := by
      obtain h' := ineq_aux (A / D) (D / A) (by positivity) (by positivity)
      simp at h'
      field_simp at h'
      field_simp
      exact h'
    have ineq5 : A / C + C / A ≥ 2 := by
      obtain h' := ineq_aux (A / C) (C / A) (by positivity) (by positivity)
      simp at h'
      field_simp at h'
      field_simp
      exact h'
    have ineq6 : B / D + D / B ≥ 2 := by
      obtain h' := ineq_aux (B / D) (D / B) (by positivity) (by positivity)
      simp at h'
      field_simp at h'
      field_simp
      exact h'
    have aux1 : A / A = 1 := by 
      apply div_self
      positivity
    have aux2 : B / B = 1 := by
      apply div_self
      positivity
    have aux3 : C / C = 1 := by
      apply div_self
      positivity
    have aux4 : D / D = 1 := by
      apply div_self
      positivity
    calc 
      _ =  (A + B + C + D) * (1 / A) + (A + B + C + D) * (1 / B) + (A + B + C + D) * (1 / C) + (A + B + C + D) * (1 / D) := by linarith
      _ = A / A + B / B + C / C + D / D + (B / A + A / B ) +  (C / B + B / C) + (D / C + C / D) + (A / D + D / A) + (A / C + C / A) + (B / D + D / B) := by 
        rw [eq3, eq4, eq5 ,eq6]
        ring
      _ ≥ 4 + 2 + 2 + 2 + 2 + 2 + 2 := by linarith [ineq1, ineq2, ineq3, ineq4, ineq5, ineq6]
      _ = 16 := by norm_num
  have ineq2 : E * (1 / A + 1 / B + 1 / C + 1 / D) - 4 ≥ 4 / 3 := by 
    have aux : E * (1 / A + 1 / B + 1 / C + 1 / D)≥ 16 / 3 := by 
      rw [←eq2] at ineq1
      refine (div_le_iff₀ ?_).mpr ?_
      · positivity
      · linarith only [ineq1]
    linarith
  rw [←eq1] at ineq2
  exact ineq2