import Mathlib

theorem algebra_300154 (f : ℝ → ℝ) (p : ℝ) (hp : 0 < p ∧ p < 15)
    (hf : ∀ x, f x = x - p + abs (x - 15 + x - p - 15)) :
    IsLeast {y | ∃ x, x ∈ Set.Icc p 15 ∧ f x = y} 15 := by
  constructor
  · -- Show 15 belongs to the set
    use 15
    constructor
    · -- Show that 15 ∈ [p, 15]
      rcases hp with ⟨hp1, hp2⟩
      exact ⟨by linarith, by linarith⟩
    · -- Compute f(15)
      rw [hf 15]
      have hp1 : 0 < p := hp.1
      have hp2 : p < 15 := hp.2
      have h1 : abs (15 - 15 + 15 - p - 15) = abs (-p) := by ring_nf
      rw [h1]
      have h2 : abs (-p : ℝ) = p := by
        rw [abs_neg]
        rw [abs_of_pos]
        linarith
      rw [h2]
      linarith
  · -- Show no value less than 15 belongs to the set
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rcases hx with ⟨hx1, hx2⟩
    rw [hf x] at hfx
    have h2 : (x - 15 + x - p - 15 : ℝ) = 2 * x - p - 30 := by ring
    rw [h2] at hfx
    have h3 : 2 * x - p - 30 < 0 := by
      linarith [hp.1, hp.2, hx1, hx2]
    rw [abs_of_neg h3] at hfx
    nlinarith [hp.1, hp.2, hx1, hx2]