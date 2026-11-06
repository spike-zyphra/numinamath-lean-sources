import Mathlib

theorem algebra_217249 (f : ℝ → ℝ) (hpos : ∀ x, 0 < x → 1 < f x)
    (hf : ∀ x y, f (x + y) = f x * f y) :
    StrictMono f := by
  have h1 : f 0 = 1 := by 
    have h2 := hf 0 0
    simp at h2
    have h3 : f 0 * (f 0 - 1) = 0 := by linarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- f 0 = 0
      exfalso
      have h6 := hf 1 0
      norm_num [h4] at h6
      linarith [hpos 1 (show (0 : ℝ) < 1 by norm_num)]
    · -- f 0 - 1 = 0
      linarith
  have h2 : ∀ x, 0 < f x := by
    intro x
    have h3 := hf x (-x)
    simp [show f 0 = 1 by exact h1] at h3
    by_cases h4 : x > 0
    · -- x > 0
      have h5 : 1 < f x := hpos x h4
      nlinarith
    · -- x ≤ 0
      by_cases h5 : x < 0
      · -- x < 0
        have h6 : 0 < -x := by linarith
        have h7 : 1 < f (-x) := hpos (-x) h6
        nlinarith
      · -- x = 0
        have h3 : x = (0 : ℝ) := by linarith
        rw [h3]
        nlinarith [h1]
  intro a b hab
  have h4 : 0 < b - a := by linarith
  have h5 : 1 < f (b - a) := hpos (b - a) h4
  have h8 : f b = f a * f (b - a) := by
    specialize hf a (b - a)
    have h7 : a + (b - a) = b := by linarith
    rw [h7] at hf
    linarith
  nlinarith [h8, h5, h2 a, h2 (b - a)]