import Mathlib

theorem algebra_163419 (α β : ℝ) :
    Real.sin (2 * α - β) ^ 2 - Real.sin (2 * α) ^ 2 - Real.sin β ^ 2 =
    -2 * Real.sin (2 * α) * Real.sin β * Real.cos (2 * α - β) := by
        have h1 : Real.sin (2 * α - β) = Real.sin (2 * α) * Real.cos β - Real.cos (2 * α) * Real.sin β := by
            rw [Real.sin_sub]
        have h2 : Real.cos (2 * α - β) = Real.cos (2 * α) * Real.cos β + Real.sin (2 * α) * Real.sin β := by
            rw [Real.cos_sub]
        rw [h1, h2]
        ring_nf
        <;> simp [Real.sin_sq, Real.cos_sq]
        <;> ring_nf
        <;> simp [Real.sin_sq, Real.cos_sq]
        <;> ring