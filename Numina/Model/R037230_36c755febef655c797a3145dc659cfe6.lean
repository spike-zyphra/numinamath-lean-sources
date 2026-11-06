import Mathlib

theorem algebra_289186 :
  {m : ℝ | ∀ x : ℝ, (4 - m) * x ^ 2 - 3 * x + 4 + m > 0} =
  Set.Ioo (-Real.sqrt 55 / 2) (Real.sqrt 55 / 2) := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- First direction: if ∀x, quadratic > 0, then m ∈ interval
    intro h
    have hm1 : m < 4 := by
      by_contra h1
      push_neg at h1
      have h1' : m ≥ 4 := by linarith
      have h2 := h 10
      nlinarith 
    have hm2 : m ^ 2 < 55 / 4 := by
      by_contra h7
      push_neg at h7
      have hm3 : 4 - m > 0 := by
        nlinarith
      have hm4 : 4 * m ^ 2 - 55 ≥ 0 := by
        nlinarith
      have h1 := h ( (3 + Real.sqrt (4 * m ^ 2 - 55)) / (2 * (4 - m)) )
      field_simp [(show (4 - m : ℝ) ≠ 0 by nlinarith), hm4 ] at h1
      have h8 : 0 ≤ (4 * m ^ 2 - 55 : ℝ) := hm4
      have h9 : Real.sqrt (4 * m ^ 2 - 55) ^ 2 = (4 * m ^ 2 - 55 : ℝ) := by
        rw [Real.sq_sqrt]
        linarith
      have h10 : (4 - m) * ((3 + Real.sqrt (4 * m ^ 2 - 55)) / (2 * (4 - m))) ^ 2 - 3 * ((3 + Real.sqrt (4 * m ^ 2 - 55)) / (2 * (4 - m))) + 4 + m ≤ 0 := by
        have h1' : (4 - m) * ((3 + Real.sqrt (4 * m ^ 2 - 55)) / (2 * (4 - m))) ^ 2 - 3 * ((3 + Real.sqrt (4 * m ^ 2 - 55)) / (2 * (4 - m))) + 4 + m = 
            ((4 - m) * (3 + Real.sqrt (4 * m ^ 2 - 55)) ^ 2 - 3 * (3 + Real.sqrt (4 * m ^ 2 - 55)) * (2 * (4 - m)) + 4 * (2 * (4 - m)) ^ 2 + m * (2 * (4 - m)) ^ 2) / ((2 * (4 - m)) ^ 2) := by 
          field_simp [(show (4 - m : ℝ) ≠ 0 by nlinarith)]
          <;> ring
        rw [h1']
        have h11 : ((4 - m) * (3 + Real.sqrt (4 * m ^ 2 - 55)) ^ 2 - 3 * (3 + Real.sqrt (4 * m ^ 2 - 55)) * (2 * (4 - m)) + 4 * (2 * (4 - m)) ^ 2 + m * (2 * (4 - m)) ^ 2) ≤ 0 := by
          nlinarith [Real.sqrt_nonneg (4 * m ^ 2 - 55), h9, sq_nonneg (Real.sqrt (4 * m ^ 2 - 55)), sq_nonneg (Real.sqrt (4 * m ^ 2 - 55) - 3), sq_nonneg (Real.sqrt (4 * m ^ 2 - 55) / 2)]
        apply div_nonpos_of_nonpos_of_nonneg 
        linarith 
        positivity 
      nlinarith 
    have h7 : -Real.sqrt 55 / 2 < m := by
      nlinarith [Real.sqrt_nonneg 55, Real.sq_sqrt (show 0 ≤ (55 : ℝ) by nlinarith)]
    have h8 : m < Real.sqrt 55 / 2 := by
      nlinarith [Real.sqrt_nonneg 55, Real.sq_sqrt (show 0 ≤ (55 : ℝ) by nlinarith)]
    constructor
    · linarith
    · linarith
  · -- Now prove the converse: if m ∈ interval, then ∀x, quadratic > 0
    rintro ⟨hm1, hm2⟩
    have hm3 : m ^ 2 < (55 : ℝ) / 4 := by
      nlinarith [Real.sqrt_nonneg 55, Real.sq_sqrt (show 0 ≤ (55 : ℝ) by nlinarith)]
    have hm4 : 4 - m > 0 := by
      nlinarith [Real.sqrt_nonneg 55, Real.sq_sqrt (show 0 ≤ (55 : ℝ) by nlinarith)]
    intro x
    have hx1 : (4 - m) * x ^ 2 - 3 * x + 4 + m > 0 := by
      nlinarith [sq_nonneg ((4 - m) * x - 3 / 2), sq_nonneg (x * (4 - m) - (3 / 2) * (4 - m)), Real.sqrt_nonneg 55, Real.sq_sqrt (show 0 ≤ (55 : ℝ) by nlinarith), sq_nonneg (Real.sqrt 55 ^ 2 - (55 : ℝ)), sq_nonneg ((4 - m) * x - 3 / 2), sq_nonneg (Real.sqrt 55 ^ 2 - (55 : ℝ))]
    exact_mod_cast hx1