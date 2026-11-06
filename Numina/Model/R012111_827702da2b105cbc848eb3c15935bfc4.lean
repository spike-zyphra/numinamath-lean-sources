import Mathlib

theorem algebra_179054 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y = x * y) (h2 : x + y + z = x * y * z) :
    1 < z ∧ z ≤ 4 / 3 := by 
  have h4 : x * y = z / (z - 1) := by
    have eq1 : x + y = x * y := by linarith
    have eq2 : x + y + z = x * y * z := by linarith
    have eq3 : x * y * z - x * y = z := by
      nlinarith 
    have h5 : x * y * (z - 1) = z := by
      nlinarith
    field_simp [(show z - 1 ≠ 0 by
      by_contra h
      have : z = 1 := by linarith
      rw [this] at h5
      nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      )] at h5 ⊢
    <;> nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h5 : z > 1 := by
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2)
    ]
  have h7 : z / (z - 1) ≥ 4 := by
    have h6 : x * y ≥ 4 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    have h8 : z / (z - 1) = x * y := by
      linarith [h4]
    linarith [h8, h6]
  have h8 : z ≤ 4 / 3 := by
    have h9 : z / (z - 1) ≥ 4 := h7
    have pos1 : 0 < z - 1 := by nlinarith
    have h11 : z ≥ 4 * (z - 1) := by
      have h12 : z / (z - 1) ≥ 4 := h9
      have h12' : z / (z - 1) - 4 ≥ 0 := by linarith
      have h13 : z / (z - 1) - 4 = (z - 4 * (z - 1)) / (z - 1) := by 
        field_simp
        <;> ring
      have h14 : (z - 4 * (z - 1)) / (z - 1) ≥ 0 := by linarith [h12']
      apply div_nonneg_iff.mp at h14 
      cases h14 with
      | inl h15 => 
        nlinarith
      | inr h16 => 
        nlinarith
    nlinarith
  constructor
  · linarith
  · linarith