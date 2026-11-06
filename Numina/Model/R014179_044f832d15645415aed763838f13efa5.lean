import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_237649 (f : ℝ → ℝ)
  (hf : f = λ x => sqrt (2 * x ^ 3 + 7 * x ^ 2 + 6 * x) / (x ^ 2 + 4 * x + 3)) :
  IsGreatest (image f (Icc 0 3)) (1 / 2) := by 
  constructor
  · -- Show that 1/2 belongs to image f [0,3] 
    use Real.sqrt 3 
    constructor
    · -- Show sqrt 3 is in [0,3] 
      have h1 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      have h2 : Real.sqrt 3 ≤ 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show 0 ≤ 3 by norm_num)]
      exact ⟨h1, h2⟩
    · -- Show f(sqrt 3) = 1/2
      rw [hf]
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h30 : Real.sqrt 3 ^ 2 = 3 := h3
      have h31 : Real.sqrt 3 ^ 3 = Real.sqrt 3 * 3 := by 
        calc
          Real.sqrt 3 ^ 3 = Real.sqrt 3 * (Real.sqrt 3 ^ 2) := by ring 
          _ = Real.sqrt 3 * 3 := by rw [h30]
      have h32 : 2 * Real.sqrt 3 ^ 3 + 7 * Real.sqrt 3 ^ 2 + 6 * Real.sqrt 3 = 12 * Real.sqrt 3 + 21 := by 
        rw [h31, h30]
        nlinarith 
      have h33 : Real.sqrt (2 * Real.sqrt 3 ^ 3 + 7 * Real.sqrt 3 ^ 2 + 6 * Real.sqrt 3) = Real.sqrt (12 * Real.sqrt 3 + 21) := by 
        rw [h32]
      have h34 : Real.sqrt (12 * Real.sqrt 3 + 21) = 3 + 2 * Real.sqrt 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, sq_nonneg (3 + 2 * Real.sqrt 3)]
      have h35 : Real.sqrt (2 * Real.sqrt 3 ^ 3 + 7 * Real.sqrt 3 ^ 2 + 6 * Real.sqrt 3) = 3 + 2 * Real.sqrt 3 := by 
        rw [h33, h34]
      have h36 : (Real.sqrt 3 ^ 2 + 4 * Real.sqrt 3 + 3) = 6 + 4 * Real.sqrt 3 := by 
        rw [h30]
        nlinarith [Real.sqrt_nonneg 3]
      simp only [h35, h36]
      field_simp 
      <;> ring_nf <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Show that 1/2 is greatest
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [hf]
    -- Need to show that f x ≤ 1/2
    have hx1 : 0 ≤ x := by 
      have h : x ∈ Icc (0 : ℝ) 3 := hx
      simp at h 
      linarith 
    have hx2 : x ≤ 3 := by
      have h : x ∈ Icc (0 : ℝ) 3 := hx
      simp at h 
      linarith 
    have h2 : sqrt (2 * x ^ 3 + 7 * x ^ 2 + 6 * x) / (x ^ 2 + 4 * x + 3) ≤ (1 / 2 : ℝ) := by 
      have h3 : x ^ 2 + 4 * x + 3 > 0 := by 
        nlinarith [sq_nonneg (x + 1 : ℝ), sq_nonneg (x + 3 : ℝ), hx1, hx2]
      apply (div_le_iff₀ (by nlinarith)).mpr
      have h7 : sqrt (2 * x ^ 3 + 7 * x ^ 2 + 6 * x) ≤ (1 / 2 : ℝ) * (x ^ 2 + 4 * x + 3) := by
        have h8 : (2 * x ^ 3 + 7 * x ^ 2 + 6 * x : ℝ) ≤ ( (1 / 4) * (x ^ 2 + 4 * x + 3) ^ 2 ) := by
          nlinarith [sq_nonneg (x ^ 2 - 3 : ℝ), sq_nonneg (x : ℝ), sq_nonneg (x - Real.sqrt 3 : ℝ), sq_nonneg (x + Real.sqrt 3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
        have h9 : sqrt (2 * x ^ 3 + 7 * x ^ 2 + 6 * x) ≤ sqrt (( (1 / 4) * (x ^ 2 + 4 * x + 3) ^ 2 )) := Real.sqrt_le_sqrt (by nlinarith)
        have h10 : sqrt (( (1 / 4) * (x ^ 2 + 4 * x + 3) ^ 2 )) = (1 / 2 : ℝ) * (x ^ 2 + 4 * x + 3) := by
          calc 
            sqrt (( (1 / 4) * (x ^ 2 + 4 * x + 3) ^ 2 : ℝ)) = sqrt (( (x ^ 2 + 4 * x + 3) / 2 ) ^ 2 ) := by ring_nf
            _ = (x ^ 2 + 4 * x + 3) / 2 := by
              rw [Real.sqrt_sq (by nlinarith [sq_nonneg (x ^ 2 + 4 * x + 3 / 2 : ℝ), sq_nonneg (x ^ 2 + 4 * x + 3 - 1 / 2 * (x ^ 2 + 4 * x + 3) : ℝ), hx1, hx2]
                )]
              <;> nlinarith 
            _ = (1 / 2 : ℝ) * (x ^ 2 + 4 * x + 3) := by ring
        linarith [h9, h10]
      linarith 
    simp only 
    all_goals linarith [h2]