import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_245774 {f : ℝ → ℝ} (hf : f = λ x => (x + 1)^2 / (x^2 + 1)) :
    MonotoneOn f (Icc (-1) 1) ∧ AntitoneOn f (Iic (-1)) ∧ AntitoneOn f (Ici 1) := by
  constructor
  · -- Prove that f is monotone on [-1, 1]
    intro x hx y hy hxy
    rw [hf]
    simp at *
    have h1 : -1 ≤ x := hx.1
    have h2 : x ≤ 1 := hx.2
    have h3 : -1 ≤ y := hy.1
    have h4 : y ≤ 1 := hy.2
    have h5 : x ≤ y := hxy
    have h10 : (x + 1) ^ 2 / (x ^ 2 + 1) ≤ (y + 1) ^ 2 / (y ^ 2 + 1) := by
      have h11 : 0 < x^2 + 1 := by
        nlinarith [sq_nonneg x]
      have h12 : 0 < y^2 + 1 := by
        nlinarith [sq_nonneg y]
      have h13 : (x + 1) ^ 2 * (y ^ 2 + 1) ≤ (y + 1) ^ 2 * (x ^ 2 + 1) := by
        have h : (x + 1) ^ 2 * (y ^ 2 + 1) - (y + 1) ^ 2 * (x ^ 2 + 1) ≤ 0 := by
          have h7 : x ≤ y := hxy
          have h8 : -1 ≤ x := hx.1
          have h9 : x ≤ 1 := hx.2
          have h10 : -1 ≤ y := hy.1
          have h11 : y ≤ 1 := hy.2
          nlinarith [mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ 1 - x * y by nlinarith), sq_nonneg (x - y), sq_nonneg (x * y - 1), mul_nonneg (show 0 ≤ 1 - x by nlinarith) (show 0 ≤ 1 - y by nlinarith), mul_nonneg (show 0 ≤ x + 1 by nlinarith) (show 0 ≤ y + 1 by nlinarith)]
        linarith
      have h14 : 0 < (x ^ 2 + 1) * (y ^ 2 + 1) := by
        positivity
      have h15 : (x + 1) ^ 2 / (x ^ 2 + 1) ≤ (y + 1) ^ 2 / (y ^ 2 + 1) := by
        have h16 : (x + 1) ^ 2 / (x ^ 2 + 1) ≤ (y + 1) ^ 2 / (y ^ 2 + 1) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          linarith
        linarith
      linarith
    exact h10
  constructor
  · -- Prove that f is antitone on (-∞, -1]
    intro x hx y hy hxy
    rw [hf]
    simp at *
    have h1 : x ≤ -1 := hx
    have h2 : y ≤ -1 := hy
    have h3 : x ≤ y := hxy
    have h10 : (x + 1)^2 / (x^2 + 1) ≥ (y + 1)^2 / (y^2 + 1) := by
      have h11 : 0 < x^2 + 1 := by
        nlinarith [sq_nonneg x]
      have h12 : 0 < y^2 + 1 := by
        nlinarith [sq_nonneg y]
      have h13 : (x + 1) ^ 2 * (y ^ 2 + 1) ≥ (y + 1) ^ 2 * (x ^ 2 + 1) := by
        have h : (x + 1) ^ 2 * (y ^ 2 + 1) - (y + 1) ^ 2 * (x ^ 2 + 1) ≥ 0 := by
          have h1 : x ≤ y := hxy
          have h2 : x ≤ -1 := hx
          have h3 : y ≤ -1 := hy
          nlinarith [mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ x * y - 1 by nlinarith), sq_nonneg (x - y), sq_nonneg (x * y - 1), mul_nonneg (show 0 ≤ -x - 1 by nlinarith) (show 0 ≤ -y - 1 by nlinarith), mul_nonneg (show 0 ≤ -x by nlinarith) (show 0 ≤ -y by nlinarith)]
        linarith
      have h14 : 0 < (x ^ 2 + 1) * (y ^ 2 + 1) := by
        positivity
      have h15 : (x + 1) ^ 2 / (x ^ 2 + 1) ≥ (y + 1) ^ 2 / (y ^ 2 + 1) := by
        have h16 : (x + 1) ^ 2 / (x ^ 2 + 1) ≥ (y + 1) ^ 2 / (y ^ 2 + 1) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          linarith
        linarith
      linarith
    exact h10
  · -- Prove that f is antitone on [1, ∞)
    intro x hx y hy hxy
    rw [hf]
    simp at *
    have h1 : 1 ≤ x := hx
    have h2 : 1 ≤ y := hy
    have h3 : x ≤ y := hxy
    have h10 : (x + 1)^2 / (x^2 + 1) ≥ (y + 1)^2 / (y^2 + 1) := by
      have h11 : 0 < x^2 + 1 := by
        nlinarith [sq_nonneg x]
      have h12 : 0 < y^2 + 1 := by
        nlinarith [sq_nonneg y]
      have h13 : (x + 1) ^ 2 * (y ^ 2 + 1) ≥ (y + 1) ^ 2 * (x ^ 2 + 1) := by
        have h : (x + 1) ^ 2 * (y ^ 2 + 1) - (y + 1) ^ 2 * (x ^ 2 + 1) ≥ 0 := by
          have h1 : x ≤ y := hxy
          have h2 : 1 ≤ x := hx
          have h3 : 1 ≤ y := hy
          nlinarith [mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ x * y - 1 by nlinarith), sq_nonneg (x - y), sq_nonneg (x * y - 1), mul_nonneg (show 0 ≤ x - 1 by nlinarith) (show 0 ≤ y - 1 by nlinarith)]
        linarith
      have h14 : 0 < (x ^ 2 + 1) * (y ^ 2 + 1) := by
        positivity
      have h15 : (x + 1) ^ 2 / (x ^ 2 + 1) ≥ (y + 1) ^ 2 / (y ^ 2 + 1) := by
        have h16 : (x + 1) ^ 2 / (x ^ 2 + 1) ≥ (y + 1) ^ 2 / (y ^ 2 + 1) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          linarith
        linarith
      linarith
    exact h10