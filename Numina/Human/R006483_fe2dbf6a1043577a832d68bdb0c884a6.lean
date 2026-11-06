import Mathlib


theorem number_theory_637596 (x y : ℕ) (k : ℕ) (hx : 0 < x) (hy : 0 < y) (hk : 2 ≤ k)
  (h : ¬∃ z, z^k = y) (h' : y < x^k) :
  Int.fract (x + (y : ℝ) ^ (1 / k : ℝ))+ Int.fract (x - (y : ℝ) ^ (1 / k : ℝ)) = (1 : ℤ) := by 
  -- Int.fract_lt_one
  obtain aux1 := Int.fract_lt_one ((x : ℝ) + ↑y ^ (1 / (k : ℝ)))
  obtain aux2 := Int.fract_lt_one ((x : ℝ) - ↑y ^ (1 / (k : ℝ)))
  have ineq1 : Int.fract ((x : ℝ) + ↑y ^ (1 / (k : ℝ))) + 
    Int.fract ((x: ℝ) - ↑y ^ (1 / (k : ℝ))) < 2 := by 
    linarith
  have ineq2 : Int.fract ((x : ℝ) -  ↑y ^ (1 / (k : ℝ))) > 0 := by 
    by_contra hc
    obtain nonneg1 := Int.fract_nonneg ((x : ℝ) - ↑y ^ (1 / (k : ℝ))) 
    have eq0 : Int.fract ((x : ℝ) -  ↑y ^ (1 / (k : ℝ))) = 0 := by 
      linarith
    obtain h2 := Int.fract_eq_iff.mp eq0
    simp at h2
    obtain ⟨t, ht⟩ := h2
    have aux3 : (y : ℝ)^ (k : ℝ)⁻¹ = x - t := by 
      linarith
    have pos : (y : ℝ)^ (k : ℝ)⁻¹ > 0 := by 
      positivity
    have xget : x - t > (0 : ℝ) := by 
      linarith
    have xgtt : x > t := by 
      norm_cast at xget
      omega
    have aux4 : ∃ z, z ^ k = y := by 
      use (x - t).toNat
      have aux5 : ((y : ℝ) ^ (k : ℝ)⁻¹) ^ k = (↑x - ↑t) ^ k := by 
        rw [aux3]
      have yeq : y = ((y : ℝ) ^ (k : ℝ)⁻¹) ^ k := by 
        calc 
          _ = (y : ℝ) ^ (1 : ℝ) := by 
            simp
          _ = y ^ ((k: ℝ)⁻¹ * k) := by 
            congr
            refine Eq.symm (inv_mul_cancel₀ ?_)
            norm_cast 
            linarith
          _ = _ := by   
            refine Real.rpow_mul_natCast ?_ (↑k)⁻¹ k
            norm_cast
            linarith
      have aux6 : (↑x - t).toNat ^ (k: ℝ) = (y: ℝ) := by 
        rw [yeq, aux3]
        norm_cast
        simp
        have aux : (↑x - t) ⊔ 0 = (x - t) := by 
          omega
        rw [aux]
      norm_cast at aux6 
    exact h aux4
  -- use Int.fract_eq_iff to explicit express the fraction part.
  have eq1 : Int.fract ((x : ℝ) + (y : ℝ) ^ (1 / (k : ℝ))) = 
    (y : ℝ) ^ (1 / (k : ℝ)) - ⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ := by 
    refine Int.fract_eq_iff.mpr ?_ 
    constructor
    have aux : (y : ℝ) ^ (1 / (k : ℝ)) ≥  ↑⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ := by 
      exact Int.floor_le ((y : ℝ) ^ (1 / (k : ℝ)))
    linarith
    constructor
    have aux : (y : ℝ) ^ (1 / (k : ℝ)) <  ↑⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ + 1 := by 
      exact Int.lt_floor_add_one ((y : ℝ) ^ (1 / (k : ℝ)))
    linarith
    use (x + ⌊(y : ℝ) ^ (1 / (k : ℝ))⌋)
    ring_nf 
    norm_cast
  -- use Int.fract_eq_iff to explicit express the fraction part.
  have eq2 : Int.fract ((x : ℝ) - (y : ℝ) ^ (1 / (k : ℝ))) = 
    1 + ⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ - (y : ℝ) ^ (1 / (k : ℝ)) := by 
    refine Int.fract_eq_iff.mpr ?_ 
    constructor
    have aux : (y : ℝ) ^ (1 / (k : ℝ)) <  ↑⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ + 1 := by 
      exact Int.lt_floor_add_one ((y : ℝ) ^ (1 / (k : ℝ)))
    linarith
    constructor
    have aux : (y : ℝ) ^ (1 / (k : ℝ)) >  ↑⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ := by 
      by_contra hc 
      simp at hc
      have aux : (y : ℝ) ^ (1 / (k : ℝ)) ≥  ↑⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ := by 
        exact Int.floor_le ((y : ℝ) ^ (1 / (k : ℝ)))
      simp at aux
      have : (y : ℝ) ^ (k : ℝ)⁻¹ = ↑⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ := by
        simp
        linarith
      let t := ⌊(y : ℝ) ^ (1 / (k : ℝ))⌋ 
      have t_pow : (t : ℝ) ^ (k : ℝ) = y := by 
        unfold t
        rw [←this]
        calc 
          _ = (y: ℝ) ^ ((k : ℝ)⁻¹ * k) := by 
            refine Eq.symm (Real.rpow_mul ?_ (↑k)⁻¹ ↑k)
            norm_cast
            linarith
          _ = y ^ (1 : ℝ) := by 
            congr
            refine inv_mul_cancel₀ ?_
            norm_cast 
            linarith
          _ = y := by 
            simp
      have hcontra : ∃ z, z ^ k = y := by 
        use t.toNat
        have tpos : t ≥ 0 := by
          have aux1 : (y : ℝ) ^ (1 / (k : ℝ)) > 0 := by 
            positivity
          unfold t
          refine Int.floor_nonneg.mpr ?_
          linarith
        norm_cast at t_pow
        zify
        rw [←t_pow]
        simp
        have aux2 : (t ⊔ 0) = t := by 
          omega
        rw [aux2] 
      exact h hcontra
    linarith
    use (x - 1 - ⌊(y : ℝ) ^ (1 / (k : ℝ))⌋)
    ring_nf 
    norm_cast
  -- since we have the explicit expression of Int.fract, we can solve it. (which is eq1, eq2)
  rw [eq1, eq2]
  ring