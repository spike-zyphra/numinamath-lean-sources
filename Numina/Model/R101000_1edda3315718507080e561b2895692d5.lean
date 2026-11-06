import Mathlib

theorem algebra_183602 {a b : ℝ × ℝ} (ha : a ≠ (0, 0)) (hb : b ≠ (0, 0))
    (h : Complex.abs (a.1 + b.1 + Complex.I * (a.2 + b.2)) =
      Complex.abs (a.1 - b.1 + Complex.I * (a.2 - b.2))) :
    a.1 * b.1 + a.2 * b.2 = 0 := by

  have h1 : Complex.abs (a.1 + b.1 + Complex.I * (a.2 + b.2)) =
    Real.sqrt ((a.1 + b.1)^2 + (a.2 + b.2)^2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> try simp [Complex.normSq]

  have h2 : Complex.abs (a.1 - b.1 + Complex.I * (a.2 - b.2)) =
    Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    <;> try simp [Complex.normSq]

  rw [h1, h2] at h

  have h3 : ((a.1 + b.1)^2 + (a.2 + b.2)^2) = ((a.1 - b.1)^2 + (a.2 - b.2)^2) := by
    rw [Real.sqrt_inj (by positivity) (by positivity) ] at h
    linarith

  nlinarith