import Mathlib

theorem algebra_276395 (x : ℝ) :
    Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 ∧
    Real.sin (2 * x) = 2 * Real.sin x * Real.cos x ∧
    Real.cos (3 * x) = Real.cos x ^ 3 - 3 * Real.cos x * Real.sin x ^ 2 ∧
    Real.sin (3 * x) = 3 * Real.cos x ^ 2 * Real.sin x - Real.sin x ^ 3 := by
  have h1 : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by
    have h2 : Real.cos (2 * x) = Real.cos (x + x) := by
      ring_nf
    rw [h2]
    have h3 : Real.cos (x + x) = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by
      rw [Real.cos_add]
    rw [h3]
    ring_nf
  constructor
  · -- Show that $\cos(2x) = \cos^2 x - \sin^2 x$
    exact h1
  constructor
  · -- Show that $\sin(2x) = 2 \sin x \cdot \cos x$
    have h3 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
      rw [Real.sin_two_mul]
    exact h3
  constructor
  · -- Show that $\cos(3x) = \cos^3 x - 3 \cos x \cdot \sin^2 x$
    have h3_eq : Real.cos (3 * x) = Real.cos x ^ 3 - 3 * Real.cos x * Real.sin x ^ 2 := by
      have h4 : Real.cos (3 * x) = Real.cos (2 * x + x) := by
        ring_nf
      rw [h4]
      have h5 : Real.cos (2 * x + x) = Real.cos (2 * x) * Real.cos x - Real.sin (2 * x) * Real.sin x := by
        rw [Real.cos_add]
      rw [h5]
      rw [show Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 by exact h1]
      rw [show Real.sin (2 * x) = 2 * Real.sin x * Real.cos x by
        have h3 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
          rw [Real.sin_two_mul]
        linarith [h3]
        ]
      ring_nf
    exact h3_eq
  · -- Show that $\sin(3x) = 3 \cos^2 x \cdot \sin x - \sin^3 x$
    have h3_eq : Real.sin (3 * x) = 3 * Real.cos x ^ 2 * Real.sin x - Real.sin x ^ 3 := by
      have h4 : Real.sin (3 * x) = Real.sin (2 * x + x) := by
        ring_nf
      rw [h4]
      have h5 : Real.sin (2 * x + x) = Real.sin (2 * x) * Real.cos x + Real.cos (2 * x) * Real.sin x := by
        rw [Real.sin_add]
      rw [h5]
      rw [show Real.sin (2 * x) = 2 * Real.sin x * Real.cos x by
        have h3 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
          rw [Real.sin_two_mul]
        linarith [h3]
        ]
      rw [show Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 by exact h1]
      ring_nf
    exact h3_eq