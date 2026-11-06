import Mathlib

theorem negated_algebra_29003 (f g : ℝ → ℝ)
    (hfg : ∀ x y, f (x + g y)
    = 2 * x + y) : ∀ x y, g (x + f y) = x / 2 + y := by
  have h1 : ∀ y, f (g y) = y := by
    intro y
    specialize hfg 0 y
    norm_num at hfg
    simpa using hfg
  have h2 : ∀ x, f (x + g 0) = 2 * x := by
    intro x
    specialize hfg x 0
    simpa using hfg
  have h3 : ∀ z, f z = 2 * (z - g 0) := by
    intro z
    have h4 : f z = 2 * (z - g 0) := by
      have h5 : f ((z - g 0) + g 0) = 2 * (z - g 0) := by
        specialize h2 (z - g 0)
        simpa using h2
      have h6 : (z - g 0 : ℝ) + g 0 = z := by
        ring
      rw [h6] at h5
      linarith
    linarith
  have h4 : ∀ z, g z = (z + 2 * (g 0)) / 2 := by
    intro z
    have h5 : f (g z) = z := by 
      apply h1
    rw [h3 (g z) ] at h5
    linarith
  intro x y
  have h7 : f y = 2 * (y - g 0) := by
    apply h3
  have h8 : x + f y = x + 2 * (y - g 0) := by
    rw [h7]
  have h9 : g (x + f y) = (x + f y + 2 * (g 0)) / 2 := by
    specialize h4 (x + f y)
    simpa using h4
  rw [h9]
  rw [h8]
  ring_nf