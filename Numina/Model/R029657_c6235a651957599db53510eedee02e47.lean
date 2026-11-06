import Mathlib


open BigOperators Real Set


lemma lemma_1 (g : ℝ → ℝ) (hg : g = λ u => -2 * u ^ 2 - u + 1)
  (u : ℝ) (hu : u ∈ Icc (-1 / 2) (1 / 2)) :
  g u ∈ Icc 0 (9 / 8) := by
  rw [hg]
  rcases hu with ⟨hu1, hu2⟩
  simp at *
  constructor
  ·
    nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg (u + 1 / 4), sq_nonneg (u + 1 / 2)]
  ·
    nlinarith [sq_nonneg (u + 1 / 4), sq_nonneg (u - 1 / 2), sq_nonneg (u - (-1 / 4)), sq_nonneg (u + 1 / 2)]


theorem algebra_231045 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin x ^ 4 - sin x * cos x + cos x ^ 4) :
  range f = {y | 0 ≤ y ∧ y ≤ 9 / 8} := by
  ext y
  simp only [mem_range, Set.mem_setOf_eq]
  constructor
  · -- First direction: if y in range f, then y in {0 ≤ y ≤ 9/8}
    intro hy
    rcases hy with ⟨x, hx⟩
    have h1 : f x = sin x ^ 4 - sin x * cos x + cos x ^ 4 := h₀ x
    rw [h1] at hx
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h3 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 := by
      calc
        sin x ^ 4 + cos x ^ 4
          = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x * cos x) ^ 2 := by ring
        _ = 1 ^ 2 - 2 * (sin x * cos x) ^ 2 := by rw [h2]
        _ = 1 - 2 * (sin x * cos x) ^ 2 := by ring

    have h4 : sin x ^ 4 - sin x * cos x + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 - sin x * cos x := by
      calc
        sin x ^ 4 - sin x * cos x + cos x ^ 4
          = (sin x ^ 4 + cos x ^ 4) - sin x * cos x := by ring
        _ = (1 - 2 * (sin x * cos x) ^ 2) - sin x * cos x := by rw [h3]
        _ = 1 - 2 * (sin x * cos x) ^ 2 - sin x * cos x := by ring

    have hx2 : 1 - 2 * (sin x * cos x) ^ 2 - sin x * cos x = y := by
      linarith
    have hu1 : -1 / 2 ≤ sin x * cos x := by
      nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x + cos x), sq_nonneg (sin x - cos x), Real.sin_sq_add_cos_sq x]
    have hu2 : sin x * cos x ≤ 1 / 2 := by
      nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x + cos x), sq_nonneg (sin x - cos x), Real.sin_sq_add_cos_sq x]

    have h9 : 0 ≤ y := by
      nlinarith [sq_nonneg ((sin x * cos x) + 1 / 4), Real.sin_sq_add_cos_sq x]

    have h10 : y ≤ 9 / 8 := by
      nlinarith [sq_nonneg ((sin x * cos x) + 1 / 4), Real.sin_sq_add_cos_sq x]

    constructor <;> linarith

  · -- Second direction: for any y in {0 ≤ y ≤ 9/8}, y in range f
    intro hy
    rcases hy with ⟨hy1, hy2⟩
    use (Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2
    have h54 : f ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) = y := by
      have h1 : f ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) =
        sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) ^ 4 - sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) + cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) ^ 4 := by
        apply h₀
      rw [h1]

      have h18 : sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) ^ 2 + cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) ^ 2 = 1 := by apply Real.sin_sq_add_cos_sq
      have h100 : sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) = ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) / 2 := by
        have h19 : sin (2 * ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ)) = (-1 + Real.sqrt (1 + 8 * (1 - y))) / 2 := by
          have h15 : 2 * ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2) = Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) := by ring
          rw [h15]
          rw [Real.sin_arcsin]
          all_goals
            nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by nlinarith)]
        have h20 : sin (2 * ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ) = 2 * sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) := by
          rw [Real.sin_two_mul]
        rw [h20] at h19
        linarith
      have h3 : sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 4 + cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 4 = 1 - 2 * (sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ)) ^ 2 := by
        calc
          sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 4 + cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 4
            = (sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 2 + cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 2) ^ 2 - 2 * (sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ)) ^ 2 := by ring
          _ = 1 ^ 2 - 2 * (sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ)) ^ 2 := by rw [h18]
          _ = 1 - 2 * (sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ)) ^ 2 := by ring

      have h4 : sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 4 - sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) + cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) ^ 4 = 1 - 2 * (sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ)) ^ 2 - (sin ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ) * cos ((Real.arcsin ((-1 + Real.sqrt (1 + 8 * (1 - y))) / 2) ) / 2 : ℝ)) := by
        linarith [h3]
      rw [h4]
      rw [h100]
      nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by nlinarith)]

    linarith