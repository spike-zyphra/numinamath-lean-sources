import Mathlib

theorem algebra_224985 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + a * x + b)
    (A B : Set ℝ) (hA : A = {x | f x = x}) (hB : B = {x | f (f x) = x}) :
    (A = {-1, 3} → B = {-Real.sqrt 3, -1, Real.sqrt 3, 3}) ∧
    A ⊆ B := by

  constructor
  · -- Assume A = {-1, 3}, prove B = {-Real.sqrt 3, -1, Real.sqrt 3, 3}
    intro hA_eq
    have h1 : -1 ∈ A := by
      rw [hA_eq]
      simp
    have h2 : 3 ∈ A := by
      rw [hA_eq]
      simp
    have h_eq1 : f (-1) = -1 := by
      rw [hA] at h1
      simpa using h1
    have h_eq2 : f 3 = 3 := by
      rw [hA] at h2
      simpa using h2
    rw [hf] at h_eq1 h_eq2
    have eq_a : a = -1 := by
      nlinarith [h_eq1, h_eq2]
    have eq_b : b = -3 := by
      nlinarith [h_eq1, h_eq2, eq_a]
    ext x
    simp [hB, hf, eq_a, eq_b]
    constructor
    · -- Assume f(f(x)) = x, prove x ∈ {-Real.sqrt 3, -1, Real.sqrt 3, 3}
      intro h_eq
      have h_eq2 : (x ^ 2 - x - 3) ^ 2 - x ^ 2 = 0 := by nlinarith
      have h_eq3 : (x ^ 2 - x - 3) ^ 2 - x ^ 2 = ((x ^ 2 - x - 3 - x) * (x ^ 2 - x - 3 + x)) := by
        ring
      rw [h_eq3] at h_eq2
      cases' (mul_eq_zero.mp h_eq2) with h1 h2
      · -- Case x^2 - 2x - 3 = 0
        have h_eq4 : x ^ 2 - 2 * x - 3 = 0 := by
          nlinarith
        have : (x = 3 ∨ x = -1) := by
          have h1 : x^2 - 2 * x - 3 = (x - 3) * (x + 1) := by ring
          rw [h1] at h_eq4
          cases' (mul_eq_zero.mp h_eq4) with h2 h3
          · left
            linarith
          · right
            linarith
        tauto
      · -- Case x^2 - 3 = 0
        have h_eq5 : x ^ 2 - 3 = 0 := by
          nlinarith
        have : (x = Real.sqrt 3 ∨ x = -Real.sqrt 3) := by
          have h1 : x^2 - 3 = (x - Real.sqrt 3) * (x + Real.sqrt 3) := by
            ring_nf
            rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
            all_goals linarith
          rw [h1] at h_eq5
          cases' (mul_eq_zero.mp h_eq5) with h4 h5
          · -- Case x - Real.sqrt 3 = 0
            left
            linarith
          · -- Case x + Real.sqrt 3 = 0
            right
            linarith
        tauto
    · -- Assume x ∈ {-Real.sqrt 3, -1, Real.sqrt 3, 3}, prove f(f(x)) = x
      rintro (h | h | h | h)
      · -- x = -Real.sqrt 3
        rw [h]
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      · -- x = -1
        rw [h]
        nlinarith
      · -- x = Real.sqrt 3
        rw [h]
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (3:ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      · -- x = 3
        rw [h]
        nlinarith
  · -- Prove that A ⊆ B
    intro x hx
    rw [hA] at hx
    simp [hB] at *
    have hfx : f x = x := hx
    rw [hfx]
    all_goals nlinarith [hf x, hf (f x), hfx]