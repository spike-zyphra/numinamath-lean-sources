import Mathlib

/-A circle contains the points (0,11) and (0,−11) on its circumference and contains all points (x,y) with x^2 + y^2 < 1
in its interior. Compute the largest possible radius of the circle.-/

theorem geometry_610278: IsGreatest {R: ℝ | ∃ h k: ℝ, h ^ 2 + (11 - k) ^ 2 = R ^ 2 ∧ h ^ 2 + (-11 - k) ^ 2 = R ^ 2 ∧
  ∀ x y, x ^ 2 + y ^ 2 ≤ 1 → (x - h) ^ 2 + (y - k) ^ 2 ≤ R ^ 2} 61 := by

    constructor

    -- show that 61 is possible
    .
      simp
      use 60, 0
      refine ⟨(by norm_num), (by norm_num), ?_⟩
      intro x y h
      nlinarith

    -- show that 61 is the largest
    .
      intro R h
      rw [Set.mem_setOf] at h
      obtain ⟨h, k, h1, h2, h3⟩ := h
      have hk: k = 0 := by
        clear *- h1 h2
        nlinarith
      simp [hk] at *
      rw [← h1] at h3
      have g:= h3
      specialize h3 (-1) 0
      simp at h3
      suffices R ^ 2 ≤ 61 ^ 2 by
        clear *- this
        nlinarith
      rw [← h1]
      clear hk h2 h1
      ring_nf at h3
      replace h3: h ≤ 60 := by nlinarith
      specialize g 1 0
      simp at g
      ring_nf at g
      replace g: -60 ≤ h := by nlinarith
      nlinarith