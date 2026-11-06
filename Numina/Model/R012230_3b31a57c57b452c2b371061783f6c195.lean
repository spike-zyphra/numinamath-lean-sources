import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_91737 (a : ℝ) :
  (∃ f : ℝ → ℝ, ∀ x, f (sin x) + a * f (cos x) = cos (2 * x)) ↔ a ∈ {x | x ≠ 1} := by
  constructor
  · -- Assume there exists a function f satisfying the equation, prove a ∈ {x | x ≠ 1}
    intro h
    rcases h with ⟨f, hf⟩
    have h1 := hf (Real.pi / 2)
    have h2 := hf 0
    have h3 : f 1 + a * f 0 = -1 := by
      have h1' : f (sin (Real.pi / 2)) + a * f (cos (Real.pi / 2)) = cos (2 * (Real.pi / 2)) := by
        simpa using h1
      have h4 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have h5 : cos (Real.pi / 2) = 0 := by
        rw [Real.cos_pi_div_two]
      have h6 : cos (2 * (Real.pi / 2)) = -1 := by
        have h7 : 2 * (Real.pi / 2) = Real.pi := by ring
        rw [h7]
        rw [Real.cos_pi]
      rw [h4, h5, h6] at h1'
      linarith
    have h4 : f 0 + a * f 1 = 1 := by
      have h2' : f (sin 0) + a * f (cos 0) = cos (2 * (0 : ℝ)) := by
        simpa using h2
      have h8 : sin (0 : ℝ) = 0 := by
        simp
      have h9 : cos (0 : ℝ) = 1 := by
        simp
      have h10 : cos (2 * (0 : ℝ)) = 1 := by
        simp
      rw [h8, h9, h10] at h2'
      linarith
    by_contra ha
    have ha1 : a = 1 := by
      simpa using ha
    rw [ha1] at h3 h4
    linarith
  · -- Assume a ∈ {x | x ≠ 1}, prove ∃ f : ℝ → ℝ, ∀ x, f (sin x) + a * f (cos x) = cos (2 * x)
    intro h
    have ha1 : a ≠ 1 := by
      simpa using h
    use fun y => (2 * y ^ 2 - 1) / (a - 1)
    intro x
    have h8 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
      have h9 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
        rw [cos_two_mul, sin_sq]
        ring
      linarith
    have h7 : (2 * (sin x) ^ 2 - 1) / (a - 1) + a * ((2 * (cos x) ^ 2 - 1) / (a - 1)) = cos (2 * x) := by
      have h11 : a - 1 ≠ 0 := by
        intro h13
        apply ha1
        linarith
      have h12 : (2 * (sin x) ^ 2 - 1) + a * (2 * (cos x) ^ 2 - 1) = (a - 1) * cos (2 * x) := by
        have h13 : cos x ^ 2 = 1 - sin x ^ 2 := by
          rw [←Real.sin_sq_add_cos_sq x]
          linarith
        rw [h13]
        have h14 : (2 * (sin x) ^ 2 - 1) + a * (2 * (1 - sin x ^ 2) - 1) = (a - 1) * (1 - 2 * sin x ^ 2) := by
          nlinarith
        have h15 : (2 * (sin x) ^ 2 - 1) + a * (2 * (1 - sin x ^ 2) - 1) = (a - 1) * cos (2 * x) := by
          rw [h8] 
          nlinarith [h14]
        linarith
      field_simp [h11]
      nlinarith [h12, h8]
    simpa using h7