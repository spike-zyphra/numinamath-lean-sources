import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_106495 {f : ℝ → ℝ} (hf : f = λ x => sqrt (x + 3) - sqrt (x - 1)) :
    Set.image f (Set.Ici 1) = Set.Ioc 0 2 := by
  ext y
  simp only [hf, Set.mem_image, Set.mem_Ici, Set.mem_Ioc, Set.mem_setOf_eq]
  constructor 
  · -- First, we prove that if y is in the image, then y ∈ (0, 2]
    rintro ⟨x, hx, rfl⟩
    have hx1 : 1 ≤ x := by simpa using hx 
    have h1 : 0 < sqrt (x + 3) - sqrt (x - 1) := by 
      have h2 : sqrt (x + 3) > sqrt (x - 1) := by 
        have h3 : x + 3 > x - 1 := by linarith 
        have h4 : x - 1 ≥ 0 := by linarith 
        have h5 : x + 3 ≥ 0 := by linarith 
        have h6 : (x + 3 : ℝ) ≥ (x - 1 : ℝ) := by linarith 
        have h7 : sqrt (x + 3) > sqrt (x - 1) := by 
          apply Real.sqrt_lt_sqrt 
          all_goals 
            nlinarith 
        exact_mod_cast h7 
      linarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1)]
    have h2 : sqrt (x + 3) - sqrt (x - 1) ≤ 2 := by 
      have h3 : x - 1 ≥ 0 := by linarith 
      have h4 : x + 3 ≥ 0 := by linarith 
      have h5 : sqrt (x + 3) ≤ 2 + sqrt (x - 1) := by 
        have h3 : x - 1 ≥ 0 := by linarith 
        have h4 : x + 3 ≥ 0 := by linarith 
        have h6 : (sqrt (x + 3)) ^ 2 ≤ (2 + sqrt (x - 1)) ^ 2 := by 
          nlinarith [Real.sq_sqrt (show 0 ≤ (x + 3 : ℝ) by linarith), 
            Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by linarith), 
            Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), 
            mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (x - 1)), 
            sq_nonneg (sqrt (x + 3) - (2 + sqrt (x - 1))), 
            Real.sqrt_le_sqrt (show (x - 1 : ℝ) ≤ (x + 3 : ℝ) by linarith)
          ]
        nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1)]
      linarith [h5, Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x + 3)]
    constructor 
    · -- Show 0 < y
      linarith 
    all_goals 
      linarith
  · -- Second, we prove the reverse direction: given y ∈ (0, 2], there exists an x ≥ 1 such that f(x) = y
    rintro ⟨hy1, hy2⟩ 
    have h9 : y ≤ 2 := hy2
    have h12 : y > 0 := hy1
    use ((4 / y - y) / 2) ^ 2 + 1 
    constructor 
    · -- Show x ≥ 1 
      have h15 : ((4 / y - y) / 2) ^ 2 ≥ 0 := by positivity 
      nlinarith 
    · -- Show f(x) = y, i.e., sqrt (x + 3) - sqrt (x - 1) = y
      have h16 : ( ((4 / y - y) / 2) ^ 2 + 1 + 3 ) = ( ((y + 4 / y) / 2 ) ) ^ 2 := by 
        field_simp 
        <;> 
        nlinarith 
      have h17 : ( ((4 / y - y) / 2) ^ 2 + 1 - 1 ) = ( ( (4 / y - y) / 2 ) ) ^ 2 := by 
        nlinarith 
      have h14 : sqrt ( ((4 / y - y) / 2) ^ 2 + 1 + 3 ) = ( (y + 4 / y) / 2 ) := by 
        rw [h16] 
        have h13 : ( ( (y + 4 / y) / 2 ) ^ 2 ) ≥ 0 := by positivity 
        have h15 : sqrt ( ( ( (y + 4 / y) / 2 ) ^ 2 ) ) = ( (y + 4 / y) / 2 ) := by 
          rw [Real.sqrt_sq] 
          all_goals 
            have h7 : y > 0 := by linarith 
            have h21 : 4 / y > 0 := by 
              apply div_pos 
              all_goals 
                nlinarith 
            nlinarith [h7, h21] 
        exact_mod_cast h15 
      -- Show √(x - 1) = ( (4 / y - y) / 2 ) 
      have h20 : 4 / y - y ≥ 0 := by 
        have h9 : y ^ 2 ≤ 4 := by nlinarith 
        have h12 : y > 0 := by linarith 
        have h17 : 4 - y ^ 2 ≥ 0 := by nlinarith 
        have h15 : 4 / y - y = (4 - y ^ 2) / y := by 
          field_simp 
          <;> 
          nlinarith 
        rw [h15] 
        have h16 : y > 0 := h12 
        have h18 : (4 - y ^ 2) / y ≥ 0 := by 
          apply div_nonneg 
          all_goals 
            nlinarith 
        linarith 
      have h19 : sqrt ( ((4 / y - y) / 2) ^ 2 + 1 - 1 ) = ( (4 / y - y) / 2 ) := by 
        rw [h17] 
        have h18 : ( ( (4 / y - y) / 2 ) ^ 2 ) ≥ 0 := by positivity 
        have h16 : 4 / y - y ≥ 0 := h20 
        have h17 : 0 ≤ ( (4 / y - y) / 2 ) := by 
          have h16 : 4 / y - y ≥ 0 := h20 
          linarith 
        have h18 : sqrt ( ( ( (4 / y - y) / 2 ) ^ 2 ) ) = ( (4 / y - y) / 2 ) := by 
          rw [Real.sqrt_sq] 
          linarith 
        exact_mod_cast h18 
      rw [show sqrt ( ((4 / y - y) / 2) ^ 2 + 1 + 3 ) - sqrt ( ((4 / y - y) / 2) ^ 2 + 1 - 1 ) = sqrt ( ((4 / y - y) / 2) ^ 2 + 1 + 3 ) - sqrt ( ((4 / y - y) / 2) ^ 2 + 1 - 1 ) by rfl] 
      rw [h14, h19] 
      field_simp 
      <;> 
      nlinarith