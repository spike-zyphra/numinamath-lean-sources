import Mathlib

theorem algebra_158928 (f : ℝ → ℝ) :
    (∀ x y, f (x * y) = f x * f y - 2 * x * y) ↔
    (∀ x, f x = 2 * x) ∨ (∀ x, f x = -x) := by
  constructor
  · -- First direction: functional equation implies f(x) = 2x or f(x) = -x
    intro h
    have f00 : f 0 = f 0 * f 0 := by
      specialize h 0 0
      norm_num at h
      linarith
    have eq1 : f 0 * (f 0 - 1) = 0 := by
      nlinarith
    have eq2 : ∀ x, f 0 = f x * f 0 := by
      intro x
      specialize h x 0
      norm_num at h
      linarith
    have f0_eq_0 : f 0 = 0 := by
      by_cases h1 : f 0 = 1
      · -- f 0 = 1
        have h2 : ∀ x, f x = 1 := by
          intro x
          have eq3 := eq2 x
          rw [h1] at eq3
          linarith
        have eq3 := h 1 1
        have eq4 : f (1 * 1) = f 1 * f 1 - 2 * (1 : ℝ) * (1 : ℝ) := by
          simpa using eq3
        have eq5 : f 1 = 1 := h2 1
        rw [show 1 * 1 = (1 : ℝ) by ring] at eq4
        rw [eq5] at eq4
        linarith
      · -- f 0 ≠ 1
        cases' (mul_eq_zero.mp eq1) with h2 h3
        · -- f 0 = 0
          linarith
        · -- f 0 - 1 = 0
          exfalso
          have h1' : f 0 = 1 := by linarith
          tauto
    have eq3 := h 1 1
    have eq4 : f (1 * 1) = f 1 * f 1 - 2 * (1 : ℝ) * (1 : ℝ) := by
      simpa using eq3
    have eq5 : f 1 = f 1 * f 1 - 2 := by
      ring_nf at eq4 ⊢
      linarith
    have eq6 : (f 1 - 2) * (f 1 + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq6) with eq7 eq8
    · -- Case f 1 = 2
      have eq7' : ∀ x, f x = 2 * x := by
        intro x
        have eq8 := h x 1
        have eq9 : f (x * (1 : ℝ)) = f x * f 1 - 2 * x * (1 : ℝ) := by
          simpa using eq8
        rw [show x * (1 : ℝ) = x by ring] at eq9
        rw [show f 1 = (2 : ℝ) by linarith [eq7] ] at eq9
        linarith
      left
      exact eq7'
    · -- Case f 1 = -1
      have eq8' : ∀ x, f x = -x := by
        intro x
        have eq9 := h x 1
        have eq10 : f (x * (1 : ℝ)) = f x * f 1 - 2 * x * (1 : ℝ) := by
          simpa using eq9
        rw [show x * (1 : ℝ) = x by ring] at eq10
        rw [show f 1 = (-1 : ℝ) by linarith [eq8] ] at eq10
        linarith
      right
      exact eq8'
  · -- Second direction: prove functional equation
    rintro (h | h)
    · -- Case f x = 2 * x
      intros x y
      rw [h (x * y), h x, h y]
      all_goals ring
    · -- Case f x = -x
      intros x y
      rw [h (x * y), h x, h y]
      all_goals ring