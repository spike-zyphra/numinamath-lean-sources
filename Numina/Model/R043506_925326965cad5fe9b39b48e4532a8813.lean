import Mathlib

theorem algebra_12687 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + 2 * x + a)
    (hfb : ∀ x, f (b * x) = 4 * x ^ 2 - 4 * x + 1) :
    {x | f (a * x + b) > 0} = {x | x ≠ 1} := by
  have h1 := hfb 0
  simp [hf] at h1
  have ha : a = 1 := by
    linarith
  have h2 := hfb 1
  simp [hf, ha] at h2
  have h3 := hfb (1 / 2)
  simp [hf, ha] at h3
  have hb : b = -2 := by
    nlinarith
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  have h4 : f (a * x + b) = (x - 1) ^ 2 := by
    rw [show a * x + b = x - 2 by
      rw [hb, ha]
      all_goals ring
    ]
    rw [hf]
    rw [ha]
    all_goals ring
  rw [h4]
  constructor
  · -- Assume (x - 1) ^ 2 > 0, prove x ≠ 1
    intro h
    by_contra h'
    have : x = 1 := by
      tauto
    rw [this] at h
    nlinarith
  · -- Assume x ≠ 1, prove (x - 1) ^ 2 > 0
    intro h
    have h5 : x ≠ 1 := h
    have h6 : (x - 1) ^ 2 > 0 := by
      have h7 : x - 1 ≠ 0 := by
        intro h'
        apply h5
        linarith
      exact sq_pos_of_ne_zero h7
    linarith