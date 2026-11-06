import Mathlib

theorem algebra_187948 (a b : ℕ → ℝ) (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (hb : ∃ r, ∀ n, b n = b 0 * r ^ n) (hpos : ∀ n, a n > 0 ∧ b n > 0)
    (hsum : a 0 + a 1 + a 2 = b 0 + b 1 + b 2)
    (hprog : ∃ d, a 1 * b 1 = a 0 * b 0 + d ∧ a 2 * b 2 = a 1 * b 1 + d) :
    a 1 = b 1 := by

  rcases hprog with ⟨d, h1, h2⟩
  rcases ha with ⟨r, hr⟩
  rcases hb with ⟨s, hs⟩

  have ha1 : a 1 = a 0 * r := by
    specialize hr 1
    simpa using hr
  have ha2 : a 2 = a 0 * r ^ 2 := by
    specialize hr 2
    simpa using hr

  have hb1 : b 1 = b 0 * s := by
    specialize hs 1
    simpa using hs
  have hb2 : b 2 = b 0 * s ^ 2 := by
    specialize hs 2
    simpa using hs

  rw [ha1, ha2, hb1, hb2] at hsum

  have heq1 : a 1 * b 1 = a 0 * b 0 * (r * s) := by
    rw [ha1, hb1]
    ring

  have heq2 : a 2 * b 2 = a 0 * b 0 * (r * s) ^ 2 := by
    rw [show a 2 = a 0 * r ^ 2 by
      specialize hr 2
      simpa using hr
    ]
    rw [show b 2 = b 0 * s ^ 2 by
      specialize hs 2
      simpa using hs
    ]
    ring_nf

  rw [heq1] at h1
  rw [heq2] at h2

  have h7 : a 0 > 0 := by
    have h := hpos 0
    linarith [h.1]
  have h8 : b 0 > 0 := by
    have h := hpos 0
    linarith [h.2]

  have h9 : a 0 * b 0 > 0 := by
    nlinarith

  have h11 : (r * s - 1) ^ 2 = 0 := by
    nlinarith [show 0 < a 0 * b 0 from by positivity, sq_nonneg (r * s - 1)]
  have h12 : r * s = 1 := by
    nlinarith

  have h13 : r > 0 := by
    have h14 : a 1 > 0 := by
      have hpos1 := hpos 1
      linarith [hpos1.1]
    rw [ha1] at h14
    have h15 : a 0 * r > 0 := h14
    nlinarith [show 0 < a 0 by linarith [h7]]

  have h14 : s > 0 := by
    have h15 : b 1 > 0 := by
      have hpos1 := hpos 1
      linarith [hpos1.2]
    rw [hb1] at h15
    have h16 : b 0 * s > 0 := h15
    nlinarith [show 0 < b 0 by linarith [h8]]

  nlinarith [sq_nonneg (a 0 * r - b 0 * s), sq_nonneg (r - s), mul_pos h7 h8, mul_pos h13 h14]