import Mathlib

theorem algebra_121617 (α β : ℝ) (h : Real.sin α * Real.sin β + Real.cos α * Real.cos β = 0) :
    Real.sin (2 * α) + Real.sin (2 * β) = 0 := by
  have h1 : Real.cos (α - β) = 0 := by
    rw [Real.cos_sub]
    linarith
  have h2 : ∃ k : ℤ, α - β = Real.pi / 2 + k * Real.pi := by
    rw [Real.cos_eq_zero_iff] at h1
    rcases h1 with ⟨k, hk⟩
    refine ⟨k, by linarith [hk]⟩
  rcases h2 with ⟨k, hk⟩
  have h_eq : α = β + Real.pi / 2 + k * Real.pi := by linarith
  have h3 : Real.sin (2 * α) = - Real.sin (2 * β) := by
    rw [show 2 * α = 2 * β + Real.pi + 2 * k * Real.pi by 
      rw [h_eq]
      ring_nf
    ]
    have h4 : Real.sin (2 * β + Real.pi + 2 * k * Real.pi) = Real.sin (2 * β + Real.pi) := by
      have h5 : Real.sin (2 * β + Real.pi + 2 * k * Real.pi) = Real.sin (2 * β + Real.pi + (k : ℝ) * (2 * Real.pi)) := by ring_nf
      rw [h5]
      rw [Real.sin_add_int_mul_two_pi]
    have h6 : Real.sin (2 * β + Real.pi) = - Real.sin (2 * β) := by 
      rw [Real.sin_add_pi]
    rw [h4, h6]
  rw [h3]
  linarith