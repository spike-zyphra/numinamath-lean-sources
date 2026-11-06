import Mathlib


theorem algebra_14574 :
    {z : ℂ | Complex.abs (z - 1) = Complex.abs (z + 3) ∧ Complex.abs (z + 3) = Complex.abs (z - Complex.I)} = {-1 - Complex.I} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First implication: if z satisfies the equalities, then z = -1 - i.
    rintro ⟨h1, h2⟩
    have eq3 : Complex.abs (z - 1) = Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    have eq4 : Complex.abs (z + 3) = Real.sqrt ((z.re + 3) ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    have eq5 : Complex.abs (z - Complex.I) = Real.sqrt (z.re ^ 2 + (z.im - 1) ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [eq3] at h1
    rw [eq4] at h1
    rw [eq4] at h2
    rw [eq5] at h2
    have eq6 : (z.re - 1) ^ 2 + z.im ^ 2 = (z.re + 3) ^ 2 + z.im ^ 2 := by
      have h : Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) = Real.sqrt ((z.re + 3) ^ 2 + z.im ^ 2) := h1
      have h1 : (Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2)) ^ 2 = (Real.sqrt ((z.re + 3) ^ 2 + z.im ^ 2)) ^ 2 := by
        rw [h]
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h1
      linarith
    have eq7 : (z.re + 3) ^ 2 + z.im ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
      have h : Real.sqrt ((z.re + 3) ^ 2 + z.im ^ 2) = Real.sqrt (z.re ^ 2 + (z.im - 1) ^ 2) := h2
      have h1 : (Real.sqrt ((z.re + 3) ^ 2 + z.im ^ 2)) ^ 2 = (Real.sqrt (z.re ^ 2 + (z.im - 1) ^ 2)) ^ 2 := by
        rw [h]
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h1
      linarith
    have eq8 : z.re = -1 := by
      nlinarith
    have eq9 : z.im = -1 := by
      rw [eq8] at eq7
      nlinarith
    simp [Complex.ext_iff, eq8, eq9]
  · -- Backward direction: z = -1 - i satisfies the conditions.
    intro h
    rw [h]
    constructor
    · -- Show |z - 1| = |z + 3|
      have eq3 : Complex.abs ((-1 - Complex.I : ℂ) - 1) = Real.sqrt 5 := by
        simp [Complex.abs, Complex.normSq]
        ring_nf
      have eq4 : Complex.abs ((-1 - Complex.I : ℂ) + 3) = Real.sqrt 5 := by
        simp [Complex.abs, Complex.normSq]
        ring_nf
      rw [eq3, eq4]
    · -- Show |z + 3| = |z - i|
      have eq5 : Complex.abs ((-1 - Complex.I : ℂ) + 3) = Real.sqrt 5 := by
        simp [Complex.abs, Complex.normSq]
        ring_nf
      have eq6 : Complex.abs ((-1 - Complex.I : ℂ) - Complex.I) = Real.sqrt 5 := by
        simp [Complex.abs, Complex.normSq]
        ring_nf
      rw [eq5, eq6]