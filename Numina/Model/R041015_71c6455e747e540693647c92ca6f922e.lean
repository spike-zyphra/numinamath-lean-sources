import Mathlib

theorem algebra_604844 :
    {(x, y) : ℝ × ℝ | (x - Real.sqrt (x ^ 2 + 1)) * (y - Real.sqrt (y ^ 2 + 1)) = 1 ∧ (x ^ 2 + y + 2) * (y ^ 2 + x + 2) = 8} = {(1, -1), (-1, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- First direction: if (x, y) satisfies both equations, then (x, y) ∈ {(1, -1), (-1, 1)}
    rintro ⟨h₀, h₁⟩
    have h2 : x - Real.sqrt (x ^ 2 + 1) ≠ 0 := by
      by_contra h
      rw [h] at h₀
      norm_num at h₀
    have h3 : y - Real.sqrt (y ^ 2 + 1) ≠ 0 := by
      by_contra h
      rw [h] at h₀
      norm_num at h₀
    have h4 : (x - Real.sqrt (x ^ 2 + 1)) * (y - Real.sqrt (y ^ 2 + 1)) = 1 := h₀
    have h5 : x - Real.sqrt (x ^ 2 + 1) = -1 / (x + Real.sqrt (x ^ 2 + 1)) := by
      field_simp [(show x + Real.sqrt (x ^ 2 + 1) ≠ 0 by
        by_contra h
        have h8 : x + Real.sqrt (x ^ 2 + 1) = 0 := by linarith
        have h9 : Real.sqrt (x ^ 2 + 1) = -x := by linarith
        have h10 : Real.sqrt (x ^ 2 + 1) ≥ 0 := by positivity
        have h11 : -x ≥ 0 := by linarith
        have h12 : Real.sqrt (x ^ 2 + 1) ^ 2 = (-x) ^ 2 := by
          rw [h9]
        have h13 : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := by
          rw [Real.sq_sqrt]
          positivity
        have h14 : (-x) ^ 2 = x ^ 2 := by ring
        nlinarith
      )
      ]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith)]
    have h6 : y - Real.sqrt (y ^ 2 + 1) = -1 / (y + Real.sqrt (y ^ 2 + 1)) := by
      field_simp [(show y + Real.sqrt (y ^ 2 + 1) ≠ 0 by
        by_contra h
        have h8 : y + Real.sqrt (y ^ 2 + 1) = 0 := by linarith
        have h9 : Real.sqrt (y ^ 2 + 1) = -y := by linarith
        have h10 : Real.sqrt (y ^ 2 + 1) ≥ 0 := by positivity
        have h11 : -y ≥ 0 := by linarith
        have h12 : Real.sqrt (y ^ 2 + 1) ^ 2 = (-y) ^ 2 := by
          rw [h9]
        have h13 : Real.sqrt (y ^ 2 + 1) ^ 2 = y ^ 2 + 1 := by
          rw [Real.sq_sqrt]
          positivity
        have h14 : (-y) ^ 2 = y ^ 2 := by ring
        nlinarith
      )
      ]
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by nlinarith)]
    rw [h5, h6] at h4
    have h7 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := by
      field_simp [(show (x + Real.sqrt (x ^ 2 + 1)) ≠ 0 by
        by_contra h
        have h8 : x + Real.sqrt (x ^ 2 + 1) = 0 := by linarith
        have h9 : Real.sqrt (x ^ 2 + 1) = -x := by linarith
        have h10 : Real.sqrt (x ^ 2 + 1) ≥ 0 := by positivity
        have h11 : -x ≥ 0 := by linarith
        have h12 : Real.sqrt (x ^ 2 + 1) ^ 2 = (-x) ^ 2 := by
          rw [h9]
        have h13 : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := by
          rw [Real.sq_sqrt]
          positivity
        have h14 : (-x) ^ 2 = x ^ 2 := by ring
        nlinarith
      ), (show (y + Real.sqrt (y ^ 2 + 1)) ≠ 0 by
        by_contra h
        have h8 : y + Real.sqrt (y ^ 2 + 1) = 0 := by linarith
        have h9 : Real.sqrt (y ^ 2 + 1) = -y := by linarith
        have h10 : Real.sqrt (y ^ 2 + 1) ≥ 0 := by positivity
        have h11 : -y ≥ 0 := by linarith
        have h12 : Real.sqrt (y ^ 2 + 1) ^ 2 = (-y) ^ 2 := by
          rw [h9]
        have h13 : Real.sqrt (y ^ 2 + 1) ^ 2 = y ^ 2 + 1 := by
          rw [Real.sq_sqrt]
          positivity
        have h14 : (-y) ^ 2 = y ^ 2 := by ring
        nlinarith
      )] at h4 ⊢
      nlinarith
    have h8 : y = -x := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by nlinarith), sq_nonneg (x - y), sq_nonneg (x + y)]
    rw [show y = -x by linarith [h8]] at h₁
    have h9 : x ^ 4 + 3 * x ^ 2 - 4 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 1)]
    have h10 : x ^ 2 = 1 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 + 1), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 + 2)]
    have h11 : x = 1 ∨ x = -1 := by
      have h12 : x ^ 2 = 1 := h10
      rw [sq_eq_one_iff] at h12
      tauto
    cases h11 with
    | inl hx1 =>
      have hy1 : y = -1 := by
        linarith [h8, hx1]
      left
      simp [hx1, hy1]
    | inr hx2 =>
      have hy2 : y = 1 := by
        linarith [h8, hx2]
      right
      simp [hx2, hy2]
  · -- Second direction: if (x, y) ∈ {(1, -1), (-1, 1)}, then (x, y) satisfies both equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · -- Check the first equation for (1, -1)
        have h1 : Real.sqrt (1 ^ 2 + 1) = Real.sqrt 2 := by norm_num
        have h2 : Real.sqrt ((-1 : ℝ) ^ 2 + 1) = Real.sqrt 2 := by norm_num
        rw [h1, h2]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- Check the second equation for (1, -1)
        norm_num
    · constructor
      · -- Check the first equation for (-1, 1)
        have h1 : Real.sqrt ((-1 : ℝ) ^ 2 + 1) = Real.sqrt 2 := by norm_num
        have h2 : Real.sqrt ((1 : ℝ) ^ 2 + 1) = Real.sqrt 2 := by norm_num
        rw [h1, h2]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- Check the second equation for (-1, 1)
        norm_num