import Mathlib

theorem algebra_181011 (f : ℝ → ℝ) (hf : f = fun x => (Real.sin x + Real.cos x)^2) :
    Set.range f = {y | 0 ≤ y ∧ y ≤ 2} := by
  ext y
  simp [hf]
  constructor
  · -- Assume y in range of f
    rintro ⟨x, hx⟩
    have h1 : 0 ≤ y := by
      have h2 : (Real.sin x + Real.cos x) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith
    have h2 : (Real.sin x + Real.cos x) ^ 2 ≤ 2 := by
      have h3 : (Real.sin x + Real.cos x) ^ 2 = (Real.sin x) ^ 2 + (Real.cos x) ^ 2 + 2 * (Real.sin x * Real.cos x) := by
        ring
      rw [h3]
      have h4 : (Real.sin x) ^ 2 + (Real.cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      have h5 : -1 ≤ 2 * Real.sin x * Real.cos x ∧ 2 * Real.sin x * Real.cos x ≤ 1 := by
        have h6 : (2 * Real.sin x * Real.cos x) = Real.sin (2 * x) := by
          rw [show 2 * x = 2 * x by ring]
          rw [Real.sin_two_mul]
          <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
          <;> ring_nf <;> nlinarith
        rw [h6]
        constructor
        · -- Show -1 ≤ Real.sin (2 * x)
          linarith [Real.neg_one_le_sin (2 * x), Real.sin_le_one (2 * x)]
        · -- Show Real.sin (2 * x) ≤ 1
          linarith [Real.sin_le_one (2 * x)]
      nlinarith [h4, h5.left, h5.right, sq_nonneg (Real.sin x - Real.cos x), sq_nonneg (Real.sin x + Real.cos x)]
    constructor
    · -- Show 0 ≤ y
      linarith
    · -- Show y ≤ 2
      linarith
  · -- Assume y Goal {0 <= y, y <= 2}
    rintro ⟨hy1, hy2⟩
    use (Real.arcsin (y - 1) / 2)
    have h4 : (Real.sin (Real.arcsin (y - 1) / 2) + Real.cos (Real.arcsin (y - 1) / 2)) ^ 2 = y := by
      have h11 : (Real.sin (Real.arcsin (y - 1) / 2) + Real.cos (Real.arcsin (y - 1) / 2)) ^ 2 =
        1 + Real.sin (Real.arcsin (y - 1) / 2 * 2) := by
        have h21 : (Real.sin (Real.arcsin (y - 1) / 2) + Real.cos (Real.arcsin (y - 1) / 2)) ^ 2 =
          (Real.sin (Real.arcsin (y - 1) / 2))^2 + (Real.cos (Real.arcsin (y - 1) / 2))^2 + 2 * (Real.sin (Real.arcsin (y - 1) / 2) * Real.cos (Real.arcsin (y - 1) / 2)) := by
          ring
        rw [h21]
        have hsin2 : (Real.sin (Real.arcsin (y - 1) / 2)) ^ 2 + (Real.cos (Real.arcsin (y - 1) / 2)) ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq (Real.arcsin (y - 1) / 2)
        rw [hsin2]
        have h19 : 2 * (Real.sin (Real.arcsin (y - 1) / 2) * Real.cos (Real.arcsin (y - 1) / 2)) = Real.sin (Real.arcsin (y - 1) / 2 * 2) := by
          have h38 : Real.sin (Real.arcsin (y - 1) / 2 * 2) = 2 * Real.sin (Real.arcsin (y - 1) / 2) * Real.cos (Real.arcsin (y - 1) / 2) := by
            rw [show Real.arcsin (y - 1) / 2 * 2 = 2 * (Real.arcsin (y - 1) / 2) by ring]
            rw [Real.sin_two_mul]
            all_goals ring_nf <;> simp [Real.sin_sq, Real.cos_sq] <;> ring_nf <;> nlinarith 
          linarith [h38]
        linarith [h19]
      have h22 : Real.sin (Real.arcsin (y - 1) / 2 * 2) = y - 1 := by
        have h50 : Real.sin (Real.arcsin (y - 1) / 2 * 2) = Real.sin (Real.arcsin (y - 1)) := by
          have h58 : Real.arcsin (y - 1) / 2 * 2 = Real.arcsin (y - 1) := by ring
          rw [h58]
        rw [h50]
        have h52 : Real.sin (Real.arcsin (y - 1)) = y - 1 := by
          apply Real.sin_arcsin
          all_goals linarith
        linarith [h52]
      rw [h11, h22]
      all_goals nlinarith
      all_goals linarith
    linarith
    all_goals nlinarith