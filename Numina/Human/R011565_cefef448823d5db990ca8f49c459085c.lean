import Mathlib

open Real Set
open scoped Real

lemma sin_add' : ∀ (x y : ℝ), sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) /2 ):= by 
  intro x y
  obtain h1 := sin_add ((x + y) / 2) ((x - y) / 2)
  obtain h2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  ring_nf at h1 h2
  rw [h1, h2]
  ring_nf

theorem algebra_277953 (x α β γ : ℝ) (h1 : sin (α - β) ≠ 0) (h2 : sin (α - γ) ≠ 0) 
  (h3 : sin (β - γ) ≠ 0)
  :
  sin (x - β) * sin (x - γ) / (sin (α - β) * sin (α - γ)) +
  sin (x - γ) * sin (x - α) / (sin (β - γ) * sin (β - α)) +
  sin (x - α) * sin (x - β) / (sin (γ - α) * sin (γ - β)) = 1 := by 
  have aux1 : sin (β - α) = - sin (α - β) := by 
    rw [←Real.sin_neg]
    simp
  have aux2 : sin (γ - α) = - sin (α - γ) := by 
    rw [←Real.sin_neg]
    simp
  have aux3 : sin (γ - β) = - sin (β - γ) := by
    rw [←Real.sin_neg]
    simp
  have aux4 : -sin (γ - α) = sin (α - γ) := by linarith
  have h4 : sin (β - α) ≠ 0 := by 
    rw [aux1] -- Rewriting to express in terms of negative angle identity.
    by_contra hc
    simp at hc
    exact h1 hc
  have h5 : sin (γ - α) ≠ 0 := by
    rw [aux2] -- Rewriting to express in terms of negative angle identity.
    by_contra hc
    simp at hc
    exact h2 hc
  have h6 : sin (γ - β) ≠ 0 := by
    rw [aux3] -- Rewriting to express in terms of negative angle identity.
    by_contra hc
    simp at hc
    exact h3 hc
  -- rw [aux1, aux3, ←aux4]
  have neq1 : sin (α - β) * sin (α - γ) ≠ 0 := mul_ne_zero h1 h2
  have neq2 : sin (β - γ) * sin (β - α) ≠ 0 := mul_ne_zero h3 h4
  have neq3 : sin (γ - α) * sin (γ - β) ≠ 0 := mul_ne_zero h5 h6
  field_simp
  have eq1 : sin (α - β) * sin (x - α) * sin (x - β) + 
    sin (β - γ) * sin (x - β) * sin (x - γ) + sin (γ - α) * sin (x - γ) * sin (x - α) 
    = sin (α - γ) * sin (γ - β) * sin (β - α) := by 
    have eq2 : 4 * (sin (α - β) * sin (x - α) * sin (x - β) + 
    sin (β - γ) * sin (x - β) * sin (x - γ) + sin (γ - α) * sin (x - γ) * sin (x - α)) 
    = 4 * (sin (α - γ) * sin (γ - β) * sin (β - α)) := by 
      calc 
        _ = 4 * sin (α - β) * sin (x - α) * sin (x - β) + 
        4 * sin (β - γ) * sin (x - β) * sin (x - γ) + 4 * sin (γ - α) * sin (x - γ) * sin (x - α) := by 
          ring_nf
        _ = 2 * sin (α - β) * (cos (α - β) - cos (2 * x - α - β)) 
          + 2 * sin (β - γ) * (cos (β - γ) - cos (2 * x - β - γ))
          + 2 * sin (γ - α) * (cos (γ - α) - cos (2 * x - γ - α)) := by
          rw [cos_sub_cos, cos_sub_cos, cos_sub_cos]
          ring_nf
          have eq1 : sin (α - x) = - sin ((x - α)):= by
            rw [←sin_neg] 
            congr
            ring
          rw [eq1]
          have eq2 : sin (- x + γ) = - sin (x - γ) := by 
            rw [←sin_neg]
            congr
            ring
          rw [eq2]
          have eq3 : sin (β - x) = - sin (x - β) := by
            rw [← sin_neg]
            congr
            ring
          rw [eq3]
          ring_nf
        _ = 2 * sin (α - β) * cos (α - β) - 2 * sin (α - β) * cos (2 * x - α - β)
          + 2 * sin (β - γ) * cos (β - γ) - 2 * sin (β - γ) * cos (2 * x - β - γ)
          + 2 * sin (γ - α) * cos (γ - α) - 2 * sin (γ - α) * cos (2 * x - γ - α) := by 
          ring_nf
        _ = sin (2 * (α - β)) - (sin (2* (α - x)) + sin (2 * (x - β))) + 
          sin (2 * (β - γ)) - (sin (2 * (β - x)) + sin (2 * (x - γ))) + 
          sin (2 * (γ - α)) - (sin (2 * (γ - x)) + sin (2 * (x - α))) := by
          rw [←sin_two_mul, ←sin_two_mul, ←sin_two_mul]
          rw [sin_add', sin_add', sin_add']
          ring_nf
          have eq1 : cos (-α - β + x * 2) = cos (α + (β - x * 2)) := by 
            rw [←cos_neg]
            congr
            ring
          have eq2 : cos (-β + (x * 2 - γ)) =  cos (β - x * 2 + γ) := by 
            rw [←cos_neg]
            congr
            ring
          have eq3 : cos (-α + (x * 2 - γ)) =  cos (α - x * 2 + γ) := by
            rw [←cos_neg]
            congr
            ring
          rw [eq1, eq2, eq3]
        _ = sin (2 * (α - β)) + sin (2 * (β - γ)) + sin (2 * (γ - α)) := by 
          have bx1 : sin (2 * (β - x)) = - sin (2 * (x - β)) := by
            rw [←sin_neg]
            congr
            ring
          have gx1 : sin (2 * (γ - x)) = - sin (2 * (x - γ)) := by
            rw [←sin_neg]
            congr
            ring
          have ax1 : sin (2 * (α - x)) = - sin (2 * (x - α)) := by 
            rw [←sin_neg]
            congr
            ring
          rw [bx1, ax1, gx1]
          ring_nf
        _ = 2 * sin (α - γ) * cos (α - 2 * β + γ) + 2 * sin (γ - α) * cos (γ - α) := by 
          have aux' : sin (2 * (α - β)) + sin (2 * (β - γ)) = 
            2 * sin (α - γ) * cos (α - 2 * β + γ) := by 
            obtain ha := sin_add (α - γ) (α - 2 * β + γ)
            obtain ha' := sin_sub (α - γ) (α - 2 * β + γ)
            ring_nf at ha
            ring_nf at ha'
            calc 
              _ = sin (α * 2 - β * 2) + sin (-(γ * 2) + β * 2) := by 
                congr
                ring
                ring
              _ = _  := by 
                rw [ha, ha']
                ring_nf
          rw [aux']
          rw [sin_two_mul]
        _ = 2 * sin (α - γ) * (cos (α - 2 * β + γ) - cos (γ - α)) := by 
          rw [aux2]
          ring
        _ = 2 * sin (α - γ) * (-2 * sin (γ - β) * sin (α - β)) := by 
          rw [Real.cos_sub_cos]
          ring_nf
        _ = _ := by 
          rw [aux1]
          ring

    linarith
  rw [aux1, aux3, ←aux4]
  calc 
    _ = sin (α - β) * sin (β - γ) * sin (γ - α) * (
    sin (α - β) * sin (x - α) * sin (x - β) + 
    sin (β - γ) * sin (x - β) * sin (x - γ) + sin (γ - α) * sin (x - γ) * sin (x - α)
    ) := by 
      ring_nf
    _ = sin (α - γ) * sin (γ - β) * sin (β - α) * sin (α - β) * sin (β - γ) * sin (γ - α) := by 
      rw [eq1]
      ring
    _ = _ := by 
      rw [aux1, aux3, ←aux4]
      ring_nf