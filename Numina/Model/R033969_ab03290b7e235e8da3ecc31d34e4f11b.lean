import Mathlib

theorem algebra_228774 :
    {(x, y) : ℝ × ℝ | x > 0 ∧ y > 0 ∧ x^2 + y * Real.sqrt (x * y) = 105 ∧ y^2 + x * Real.sqrt (y * x) = 70} = {(9, 4)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First implication: if (x, y) is in the set, then (x, y) = (9, 4).
    rintro ⟨hx, hy, h1, h2⟩
    have h3 : Real.sqrt (x * y) = Real.sqrt (y * x) := by
      have h9 : x * y = y * x := by ring
      rw [show (y * x : ℝ) = x * y by ring]
    
    have h4 : Real.sqrt (x * y) = Real.sqrt (y * x) := h3
    have h7 : y ^ 2 + x * Real.sqrt (y * x) = 70 := by linarith
    have h12 : y ^ 2 + x * Real.sqrt (x * y) = 70 := by
      rw [show Real.sqrt (y * x) = Real.sqrt (x * y) by
        have h9 : x * y = y * x := by ring
        rw [show y * x = x * y by ring]
      ] at h7
      linarith
    have h13 : Real.sqrt (x * y) = 6 := by
      nlinarith [Real.sqrt_nonneg (x * y), 
        Real.sq_sqrt (show 0 ≤ x * y by positivity), 
        sq_nonneg (x - 9), sq_nonneg (y - 4), 
        mul_pos hx hy, Real.sqrt_nonneg (y * x)
      ]
    have h14 : x * y = 36 := by
      calc
        x * y = (Real.sqrt (x * y)) ^ 2 := by 
          rw [Real.sq_sqrt]
          nlinarith [show 0 ≤ x * y by positivity]
        _ = 6 ^ 2 := by 
          rw [h13]
        _ = 36 := by norm_num

    have eq1 : x ^ 2 + y * Real.sqrt (x * y) = 105 := h1
    have eq2 : y ^ 2 + x * Real.sqrt (x * y) = 70 := h12
    have eq3 : x * y = 36 := h14
    have eq4 : x ^ 2 + 6 * y = 105 := by
      rw [show Real.sqrt (x * y) = 6 by linarith [h13]] at eq1
      linarith
    have eq5 : y ^ 2 + 6 * x = 70 := by
      rw [show Real.sqrt (x * y) = 6 by linarith [h13]] at eq2
      linarith
    have eq6 : x = 9 := by
      nlinarith [sq_nonneg (x - 9 : ℝ), sq_nonneg (y - 4 : ℝ), sq_nonneg (x * y - 36), mul_pos hx hy]
    have eq7 : y = 4 := by
      nlinarith [sq_nonneg (x - 9 : ℝ), sq_nonneg (y - 4 : ℝ), sq_nonneg (x * y - 36), mul_pos hx hy]
    simp [eq6, eq7]

  · -- Second implication: (9, 4) is in the set.
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Check first equation
      have h1 : Real.sqrt ((9 : ℝ) * (4 : ℝ)) = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h1, Real.sqrt_nonneg (9 * (4 : ℝ))]
    · -- Check second equation
      have h1 : Real.sqrt ((4 : ℝ) * (9 : ℝ)) = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h1, Real.sqrt_nonneg (4 * (9 : ℝ))]