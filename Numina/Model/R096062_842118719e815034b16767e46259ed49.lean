import Mathlib

theorem algebra_160762 {x y z : ℝ} (h1 : x + y + z = 1) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (h3 : x ^ 3 + y ^ 3 + z ^ 3 = 1) :
    (x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = 0 ∧ z = 1) := by 
  have h4 : x * y + y * z + z * x = 0 := by
    have h5 : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by ring
    rw [h1] at h5
    linarith
  have h5 : x * y * z = 0 := by
    have h8 : x ^ 3 + y ^ 3 + z ^ 3 - 3 * (x * y * z) = (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - (x * y + y * z + z * x)) := by ring
    rw [h1, h2, h4] at h8
    linarith [h3, h8]

  cases' (mul_eq_zero.mp h5) with h6 h7
  cases' (mul_eq_zero.mp h6) with h8 h9
  
  · -- Case h8: x = 0
    have hx : x = 0 := h8
    have h10 : y + z = 1 := by linarith [h1, hx]
    have h11 : y * z = 0 := by
      have h_eq : x * y + y * z + z * x = 0 := by linarith [h4]
      rw [hx] at h_eq
      nlinarith
    cases' (mul_eq_zero.mp h11) with hy hz
    · -- Case h11: y = 0
      have hy' : y = 0 := by linarith
      have hz' : z = 1 := by linarith [h10, hy']
      -- Solution: (0, 0, 1)
      simp [hx, hy', hz']
      <;> tauto
  
    · -- Case hz: z = 0
      have hz' : z = 0 := by linarith
      have h13 : y = 1 := by linarith [h1, hx, hz']
      -- Solution: (0, 1, 0)
      simp [hx, h13, hz']
      <;> tauto
  
  · -- Case h9: y = 0
    have h13 : y = 0 := h9
    have h14 : x + z = 1 := by linarith [h1, h13]
    have h15 : x * z = 0 := by
      have h_eq : x * y + y * z + z * x = 0 := by linarith [h4]
      rw [h13] at h_eq
      nlinarith
    cases' (mul_eq_zero.mp h15) with hx hz
    · -- Case hx: x = 0
      have hx' : x = 0 := hx
      have hz' : z = 1 := by linarith [h14, hx']
      -- Solution: (0, 0, 1)
      simp [hx', h13, hz']
      <;> tauto
  
    · -- Case hz: z = 0
      have hz' : z = 0 := by linarith
      have h49 : x = 1 := by linarith [h14, hz']
      -- Solution: (1, 0, 0)
      simp [h49, h13, hz']
      <;> tauto
  
  · -- Case h7: z = 0
    have hz' : z = 0 := h7
    have h14 : x + y = 1 := by linarith [h1, hz']
    have h15 : x * y = 0 := by
      have h_eq : x * y + y * z + z * x = 0 := by linarith [h4]
      rw [hz'] at h_eq
      nlinarith
    cases' (mul_eq_zero.mp h15) with hx hy
    · -- Case hx: x = 0
      have hx' : x = 0 := hx
      have h13 : y = 1 := by linarith [h14, hx']
      -- Solution: (0, 1, 0)
      simp [hx', h13, hz']
      <;> tauto
  
    · -- Case hy: y = 0
      have h13 : y = 0 := by linarith
      have h49 : x = 1 := by linarith [h14, h13]
      -- Solution: (1, 0, 0)
      simp [h49, h13, hz']
      <;> tauto