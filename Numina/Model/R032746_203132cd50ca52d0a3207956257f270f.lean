import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_321264 (z : ℕ → ℂ)
  (h₀ : z 0 = 0)
  (h₁ : ∀ n, z (n + 1) = (z n)^2 + I) :
  abs (z 110) = Real.sqrt 2 := by
  -- Calculate the first few terms to identify a cycle.
  have h2 : z 1 = I := by
    specialize h₁ 0
    rw [h₀] at h₁
    norm_num [h₁]
  have h3 : z 2 = -1 + I := by
    specialize h₁ 1
    rw [h2] at h₁
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h₁ ⊢
    norm_num [h₁]
  have h4 : z 3 = -I := by
    specialize h₁ 2
    rw [h3] at h₁
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h₁ ⊢
    norm_num [h₁]
  have h5 : z 4 = -1 + I := by
    specialize h₁ 3
    rw [h4] at h₁
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h₁ ⊢
    norm_num [h₁]
  have h7 : ∀ (k : ℕ), z (2 * k + 2) = -1 + I ∧ z (2 * k + 3) = -I := by
    intro k
    induction k with
    | zero =>
      constructor
      · exact h3
      · exact h4
    | succ k ih =>
      have h_eq1 : z (2 * (k + 1) + 2) = -1 + I := by
        have eq4 : z (2 * (k + 1) + 2) = (z (2 * (k + 1) + 1)) ^ 2 + I := by
          specialize h₁ (2 * (k + 1) + 1)
          simpa using h₁
        have eq5 : z (2 * (k + 1) + 1) = -I := by
          have eq7 : z (2 * (k + 1) + 1) = (z (2 * k + 2)) ^ 2 + I := by
            specialize h₁ (2 * k + 2)
            simpa using h₁
          have h9 : z (2 * k + 2) = -1 + I := ih.1
          rw [h9] at eq7
          simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq7 ⊢
          norm_num [eq7]
        rw [eq5] at eq4
        simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq4 ⊢
        norm_num [eq4]
      have h_eq2 : z (2 * (k + 1) + 3) = -I := by
        have eq5 : z (2 * (k + 1) + 3) = (z (2 * (k + 1) + 2)) ^ 2 + I := by
          specialize h₁ (2 * (k + 1) + 2)
          simpa using h₁
        rw [h_eq1] at eq5
        simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq5 ⊢
        norm_num [eq5]
      constructor
      · exact h_eq1
      · exact h_eq2
  have h8 : ∀ (k : ℕ), z (2 * k + 2) = -1 + I := by
    intro k
    have h9 : z (2 * k + 2) = -1 + I ∧ z (2 * k + 3) = -I := h7 k
    exact h9.1
  -- Prove that z_110 = -1 + I.
  have h9 : z 110 = -1 + I := by
    specialize h8 54
    norm_num at h8 ⊢
    exact h8
  -- Compute the modulus.
  rw [h9]
  simp [Complex.abs, Complex.normSq]
  all_goals
    ring_nf