import Mathlib

theorem number_theory_639453 (n : ℕ) (hn : 3 ≤ n) (k : ℤ) (a b : ℤ)
  (h : IsUnit (a * b : ZMod n) ∧ (a * b : ZMod n)⁻¹ = (k : ZMod n)) 
  (h' : IsUnit (a + b : ZMod n)) :
  ((a + b: ZMod n)⁻¹ * ((a : ZMod n)⁻¹ + (b : ZMod n)⁻¹ )) = k := by 
  obtain ⟨h1, h2⟩ := h
  -- if an element x in ZMod n is Unit, then x⁻¹ * x = 1 in ZMod n.
  have eq1 : (a + b: ZMod n)⁻¹ * (a + b : ZMod n) = 1:= by 
    exact ZMod.inv_mul_of_unit (a + b : ZMod n) h'
  have eq2 : (a * b : ZMod n)⁻¹ * (a * b : ZMod n) = 1 := by 
    exact ZMod.inv_mul_of_unit (a * b : ZMod n) h1
  -- since a * b is unit then a and b are units.
  have isUnit_a : IsUnit (a : ZMod n) := by
    exact isUnit_of_mul_isUnit_left h1
  have isUnit_b : IsUnit (b : ZMod n) := by
    exact isUnit_of_mul_isUnit_right h1
  obtain eq3 := ZMod.inv_mul_of_unit (a : ZMod n) isUnit_a
  obtain eq4 := ZMod.inv_mul_of_unit (b : ZMod n) isUnit_b
  have eq5 : ((a + b: ZMod n)⁻¹ * ((a : ZMod n)⁻¹ + (b : ZMod n)⁻¹ )) 
    * (a * b : ZMod n) = 1 := by 
    ring_nf
    have aux1 : (a : ZMod n) * ↑b * (a + b: ZMod n)⁻¹ * (a : ZMod n)⁻¹
      = (a + b: ZMod n)⁻¹ * b := by 
      calc 
        _ = ↑b * (a + b: ZMod n)⁻¹ * ((a : ZMod n)⁻¹ * a) := by 
          ring_nf 
        _ = _ := by 
          rw [eq3]
          simp
          ring_nf
    have aux2 : ↑a * ↑b * (a + b : ZMod n)⁻¹ * (b : ZMod n)⁻¹ = (a + b: ZMod n)⁻¹ * a := by 
      calc 
        _ = ↑a * (a + b: ZMod n)⁻¹ * ((b : ZMod n)⁻¹ * b) := by
          ring_nf
        _ = _ := by
          rw [eq4]
          simp
          ring_nf
    rw [aux2, aux1]
    calc 
      _ = (a + b : ZMod n)⁻¹ * (a + b) := by ring_nf
      _ = 1 := by 
        rw [eq1]
  calc 
    _ = ((a + b: ZMod n)⁻¹ * ((a : ZMod n)⁻¹ + (b : ZMod n)⁻¹ )) * 1 := by 
      ring_nf
    _ = ((a + b: ZMod n)⁻¹ * ((a : ZMod n)⁻¹ + (b : ZMod n)⁻¹ )) 
      * (a * b : ZMod n) * k := by 
      rw [←eq2, h2]
      ring
    _ = k := by 
      rw [eq5]
      simp