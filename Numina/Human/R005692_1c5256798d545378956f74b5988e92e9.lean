import Mathlib

open Real

/-The three sides of a right triangle form a geometric sequence. 
Determine the ratio of the length of the hypotenuse to the length of the shorter leg.-/

theorem geometry_609442 (a b c : ℝ) (h0 : a > 0)
    (h3 : a^2 + b^2 = c^2) (h4 : ∃ r, b = a * r ∧ c = b * r) :
    c / a = (1 + √5) / 2 := by

    obtain ⟨r, h4, h5⟩ := h4
    simp [h4, h5] at h3
    replace h3: a ^ 2 * (r ^ 4 - r ^ 2 - 1) = 0 := by
      linarith
    simp at h3
    rcases h3 with s | s
    .
      simp [s] at h0
    .
      simp [h5, h4]
      suffices r ^ 2 = (1 + √5) / 2 by
        rw [← this]
        field_simp
        ring
      rw [show r ^ 4 = (r ^ 2) ^ 2 by ring] at s
      set q:= r ^ 2
      have lq: 0 ≤ q := by
        simp [q]
        apply sq_nonneg
      clear *- lq s
      have f: √5 ^ 2 = 5 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        norm_num
        apply sqrt_nonneg
      have u: q ^ 2 - q - 1 = (q - (1 + √5) / 2) * (q - (1 - √5) / 2) := by
        ring_nf
        simp [f]
        ring
      rw [u] at s
      clear u
      simp at s
      rcases s with s | s
      .
        linarith
      .
        absurd lq
        simp
        have r: 1 < √5 := by
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        nlinarith