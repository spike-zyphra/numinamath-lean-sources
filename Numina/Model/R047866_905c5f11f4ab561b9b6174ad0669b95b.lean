import Mathlib

theorem algebra_177697 :
    {z : ℝ | ∃ x y : ℝ , x^3 + y^3 = 2 ∧ z = x + y } =  Set.Ioc 0 2 := by
  ext z 
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · -- First, we prove that if z = x + y with x^3 + y^3 = 2, then 0 < z ≤ 2.
    rintro ⟨x, y, h1, h2⟩ 
    have h3 : z = x + y := by linarith 
    have h4 : x^3 + y^3 = 2 := h1 
    have h5 : z > 0 := by 
      by_contra h
      push_neg at h 
      have h6 : z ≤ 0 := by linarith 
      have h7 : x + y ≤ 0 := by linarith [h6, h3]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y), 
        sq_nonneg (x - (-y)), sq_nonneg (y - (-x)), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - (-y)), sq_nonneg (y - (-x)), sq_nonneg (x^2 - y^2)]
    have h8 : z ≤ 2 := by 
      have h9 : x + y > 0 := by linarith [h5, h3]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), 
        sq_nonneg (x + y - 2), sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg ((x + y) ^ 2), sq_nonneg (x * y), mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (x + y - 2))]
    constructor <;> linarith 
  · -- Now, we prove the reverse direction: if z ∈ (0, 2], then there exist real numbers x and y such that x^3 + y^3 = 2 and z = x + y.
    rintro ⟨hz1, hz2⟩ -- z ∈ (0, 2]
    have h9 : z > 0 := hz1
    have h10 : z ≤ 2 := by linarith 
    have h11 : z ^ 3 ≤ 8 := by
      have h12 : z ≤ 2 := by linarith 
      nlinarith [sq_nonneg (z - 2), sq_nonneg (z ^ 2), sq_nonneg (z + 0)]
    have h12 : (8 - z ^ 3) / (3 * z) ≥ 0 := by 
      apply div_nonneg 
      · -- Show 8 - z^3 ≥ 0 
        nlinarith [sq_nonneg (z ^ 2), sq_nonneg (z), sq_nonneg (z - 2), sq_nonneg (z ^ 2 - 4)]
      · -- Show 3 * z ≥ 0 
        nlinarith 
    have h13 : ∃ x y : ℝ, x^3 + y^3 = 2 ∧ z = x + y := by
      use (z + Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2, 
          (z - Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2
      constructor
      · -- Verify x^3 + y^3 = 2 
        have h17 : Real.sqrt ((8 - z ^ 3) / (3 * z)) ^ 2 = (8 - z ^ 3) / (3 * z) := Real.sq_sqrt (show ((8 - z ^ 3) / (3 * z)) ≥ 0 by linarith [h12])
        have h16 : ((z + Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2 ) ^3 + ((z - Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2 ) ^3 = 2 := by 
          have h17' : ((z + Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2 ) ^3 + ((z - Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2 ) ^3 = 2 := by 
            have eq1 : ((z + Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2 ) ^3 + ((z - Real.sqrt ((8 - z ^ 3) / (3 * z)) ) / 2 ) ^3 = (z ^3 + 3 * z * (Real.sqrt ((8 - z ^ 3) / (3 * z)) ) ^ 2 ) / 4 := by 
              ring_nf 
              <;> 
              nlinarith [Real.sqrt_nonneg ((8 - z ^ 3) / (3 * z)), sq_nonneg (z ^ 2), sq_nonneg (Real.sqrt ((8 - z ^ 3) / (3 * z)) ^ 2), sq_nonneg (z), mul_nonneg (Real.sqrt_nonneg ((8 - z ^ 3) / (3 * z))) (Real.sqrt_nonneg ((8 - z ^ 3) / (3 * z)) ) ]
            rw [eq1] 
            rw [h17]
            field_simp [(show z ≠ 0 by linarith)]
            <;> 
            nlinarith 
          linarith [h17']
        linarith 
      · -- Verify z = x + y 
        field_simp [(show z ≠ 0 by linarith)]
        <;> 
        nlinarith 
    tauto