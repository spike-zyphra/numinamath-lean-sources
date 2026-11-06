import Mathlib
open Set

theorem algebra_10314 (k : ℝ) (hk : k > 0) (f : ℝ → ℝ) (hf : f = fun x => x ^ k) : image f (Ici 1) = Ici 1 := by
  ext y
  simp [hf]
  constructor
  · -- Assume y in image of f
    rintro ⟨x, hx, hfx⟩
    have h1 : x ≥ 1 := by simpa using hx
    have h2 : (x : ℝ) ^ k ≥ (1 : ℝ) ^ k := by
      apply Real.rpow_le_rpow
      all_goals linarith
    have h3 : (1 : ℝ) ^ k = 1 := by
      simp
    have h4 : (x : ℝ) ^ k ≥ 1 := by
      rw [h3] at h2
      linarith
    have h5 : y ≥ 1 := by
      linarith [hfx, h4]
    linarith
  · -- Assume y ≥ 1, prove y in image of f
    intro hy
    have h1 : y ≥ 1 := by simpa using hy
    use y ^ (1 / k)
    constructor
    · -- Show that x ≥ 1
      have h3 : y ^ (1 / k) ≥ 1 := by
        have h4 : y ≥ 1 := by linarith
        have h5 : (1 / k : ℝ) > 0 := by
          have hk1 : k > 0 := hk
          positivity
        have h6 : y ^ (1 / k : ℝ) ≥ (1 : ℝ) ^ (1 / k : ℝ) := by
          apply Real.rpow_le_rpow
          all_goals linarith
        have h7 : (1 : ℝ) ^ (1 / k : ℝ) = 1 := by
          simp
        linarith
      linarith
    · -- Show that f(x) = y
      have h4 : (y ^ (1 / k : ℝ) ) ^ k = y := by
        have h5 : ((y ^ (1 / k : ℝ) ) ^ k) = y := by
          rw [← Real.rpow_mul]
          field_simp
          all_goals linarith
        linarith
      linarith