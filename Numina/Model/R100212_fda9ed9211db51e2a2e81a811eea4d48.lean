import Mathlib

theorem calculus_13158 : ∃ n : ℕ, 0 ≤ n ∧ n ≤ 180 ∧ Real.cos (n * Real.pi / 180) = Real.cos (259 * Real.pi / 180) := by
  use 101
  constructor
  · norm_num -- shows 0 ≤ 101
  constructor
  · norm_num -- shows 101 ≤ 180
  · -- shows cos(101*pi/180) = cos(259*pi/180)
    have h1 : 259 * Real.pi / 180 = 2 * Real.pi - (101 * Real.pi / 180) := by
      linarith [Real.pi_pos]
    have h2 : Real.cos (259 * Real.pi / 180) = Real.cos (101 * Real.pi / 180) := by
      rw [h1]
      have hcos : Real.cos (2 * Real.pi - (101 * Real.pi / 180)) = Real.cos (101 * Real.pi / 180) := by
        rw [show 2 * Real.pi - (101 * Real.pi / 180) = 2 * Real.pi - (101 * Real.pi / 180) by ring]
        rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
        <;> ring_nf
        <;> simp [Real.sin_sq, Real.cos_sq]
        <;> ring
      exact hcos
    linarith [h2]