import Mathlib

open Complex
/-Suppose x is a fifth root of unity. Find, in radical form, all possible values of
2*x + 1/(1+x) + x/(1+x^2) + x^2/(1+x^3) + x^3/(1+x^4)-/
theorem algebra_611401 {y: ℂ} (h: ∃ x: ℂ, x ^ 5 = 1 ∧
y = 2 * x + 1 / (1 + x) + x / (1 + x ^ 2) + x ^ 2 / (1 + x ^ 3) + x ^ 3 / (1 + x ^ 4)):
 y = 4 ∨ y = -1 - √5 ∨ y = -1 + √5 := by

  have eq1: I ^ 2 = -1 := by
    norm_num
  have eq2: I ^ 4 = 1 := by
    norm_num

  -- let's first simplify the expression
  have id: ∀ x: ℂ, x ^ 5 = 1 → 
  2 * x + 1 / (1 + x) + x / (1 + x ^ 2) + x ^ 2 / (1 + x ^ 3) + x ^ 3 / (1 + x ^ 4) = 2 * x + 2 / x := by
    intro x hx
    have id1: x / (1 + x ^ 2) + x ^ 2 / (1 + x ^ 3) = 1 / x := by
     -- we need show the denominators are not zero
      have ne1: x ≠ 0 := by
        by_contra! ne
        simp [ne] at hx
      have ne2: 1 + x ^ 2 ≠ 0 := by 
        by_contra! ne
        have o: 1 + x ^ 2 = (x + I) * (x - I) := by
          ring_nf
          simp [eq1]
          ring
        rw [o] at ne
        simp at ne
        rcases ne with ne | ne
        . replace ne: x = -I := by rw [show x = x + I - I by ring]; rw [ne]; simp
          simp [ne] at hx
          have o: (-I) ^ 5 = -I := by 
            rw [show (-I) ^ 5 = -1 * I ^ 5 by ring]
            simp
            rw [show I ^ 5 = I * I ^ 4 by ring]
            simp [eq2]
          rw [o] at hx
          replace hx: (-I) ^ 2 = 1 ^ 2 := by rw [hx]
          rw [show (-I) ^ 2 = I ^ 2 by ring] at hx
          rw [eq1] at hx
          simp at hx
          absurd hx
          norm_num
        . replace ne: x = I := by rw [show x = x - I + I by ring]; rw [ne]; simp
          simp [ne] at hx
          have o: I ^ 5 = I := by 
            rw [show I ^ 5 = I * I ^ 4 by ring]
            simp [eq2]
          rw [o] at hx
          replace hx: I ^ 2 = 1 ^ 2 := by rw [hx]
          rw [show I ^ 2 = I ^ 2 by ring] at hx
          rw [eq1] at hx
          simp at hx
          absurd hx
          norm_num 
      have ne3: 1 + x ^ 3 ≠ 0 := by
        by_contra! ne
        replace ne: x ^ 2 * (1 + x ^ 3) = 0 := by simp [ne]
        ring_nf at ne
        rw [hx] at ne
        rw [show x ^ 2 + 1 = 1 + x ^ 2 by ring] at ne
        absurd ne
        simp [ne2]
      field_simp
      ring_nf
      simp [hx]
      ring
    have id2: 1 / (1 + x) + x ^ 3 / (1 + x ^ 4) = 1 / x := by
    -- first show the denominators are not zero
      have ne1: 1 + x ≠ 0 := by
        by_contra! ne
        replace ne: x = -1 := by rw [show x = 1 + x - 1 by ring]; rw [ne]; simp
        simp [ne] at hx
        absurd hx
        norm_num
      have ne2: 1 + x ^ 4 ≠ 0 := by
        by_contra! ne
        replace ne: x * (1 +  x ^ 4) = 0 := by rw [ne]; simp
        ring_nf at ne
        rw [hx] at ne
        rw [show x + 1 = 1 + x by ring] at ne
        absurd ne
        simp [ne1]
      have ne3: x ≠ 0 := by
        by_contra! ne
        simp [ne] at hx
      field_simp
      ring_nf
      simp [hx]
      ring
    rw [show 2 * x + 1 / (1 + x) + x / (1 + x ^ 2) + x ^ 2 / (1 + x ^ 3) + x ^ 3 / (1 + x ^ 4)
    = 2 * x + (1 / (1 + x) + x ^ 3 / (1 + x ^ 4) + (x / (1 + x ^ 2) + x ^ 2 / (1 + x ^ 3))) by ring]
    rw [id1,id2]
    ring
  
  -- now we replace the expression with the simplified one
  obtain ⟨x,h⟩ := h
  rcases h with ⟨hx,h⟩
  specialize id x hx
  rw [id] at h
  clear id
  set t:= x + 1 / x with ht
  rw [show 2 * x + 2 / x = 2 * t by ring] at h
  simp [h]
  clear h
  by_cases ne: x = 1
  . simp [ne] at ht
    simp [ht]
    left
    norm_num
  -- x ≠ 1, then 1 + x + .. + x ^ 4 = 0
  . have fac: x ^ 5 - 1 = (x - 1) * (1 + x + x ^ 2 + x ^ 3 + x ^ 4) := by ring
    have hx': x ^ 5 - 1 = 0 := by rw [hx]; norm_num
    rw [hx'] at fac
    simp at fac
    replace ne: x - 1 ≠ 0 := by
      by_contra! none
      replace none: x = 1 := by rw [show x = x - 1 + 1 by ring]; rw [none]; simp
      absurd ne
      exact none
    simp [ne] at fac
    have ne0: x ≠ 0 := by
            by_contra!
            simp [this] at hx
    have eq1: 1 + x + x ^ 2 + x ^ 3 + x ^ 4 = (x ^ 2 + 1 / x ^ 2 + 2) + (x + 1 / x) - 1 := by
      have o1: x ^ 2 = 1 / x ^ 3 := by
        field_simp
        ring_nf
        exact hx
      have o2: x ^ 3 = 1 / x ^ 2 := by
        field_simp
        ring_nf
        exact hx
      have o3: x ^ 4 = 1 / x := by
        field_simp
        ring_nf
        exact hx
      rw [o1,o2,o3]
      field_simp
      ring
    rw [eq1] at fac
    clear eq1
    have eq2: (x ^ 2 + 1 / x ^ 2 + 2) + (x + 1 / x) - 1 = t ^ 2 + t - 1 := by
      simp [ht]
      field_simp
      ring
    rw [eq2] at fac
    clear eq2
    clear_value t
    have eq3: t ^ 2 + t - 1 = (t - (-1 - √5)/2) * (t - (-1 + √5)/2) := by
      ring_nf
      have o: (√5: ℂ) ^ 2 = 5 := by
        norm_cast
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        norm_num
        apply Real.sqrt_nonneg
      rw [o]
      ring_nf
    rw [eq3] at fac
    clear eq3
    simp at fac
    rcases fac with l | l
    . right
      left
      replace l: t = (-1 - ↑√5) / 2 := by 
        rw [show t = t - (-1 - ↑√5)/2 + (-1 - ↑√5)/2 by ring_nf]
        rw [l]
        simp
      rw [l]
      norm_cast
      simp
      ring
    . right
      right
      replace l: t = (-1 + ↑√5) / 2 := by 
        rw [show t = t - (-1 + ↑√5)/2 + (-1 + ↑√5)/2 by ring_nf]
        rw [l]
        simp
      rw [l]
      norm_cast
      simp
      ring