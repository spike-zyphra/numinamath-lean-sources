import Mathlib

open Polynomial

theorem algebra_251432 (f : Polynomial ℤ) (hf : f = 29 * 37 * X ^ 4 + 2 * X ^ 2 + 9) :
    ¬(∃ g : Polynomial ℤ, g = X ^ 2 + 3 ∧ g ∣ f) ∧
    ¬(∃ g : Polynomial ℤ, g = X + 1 ∧ g ∣ f) ∧
    ¬(∃ g : Polynomial ℤ, g = X ^ 2 - 3 ∧ g ∣ f) ∧
    ¬(∃ g : Polynomial ℤ, g = X ^ 2 - 2 * X - 3 ∧ g ∣ f) := by
  have h1 : f = 29 * 37 * X ^ 4 + 2 * X ^ 2 + 9 := hf
  constructor
  · -- Show that there's no polynomial g = X^2 + 3 dividing f
    rintro ⟨g, hg1, hg2⟩
    rw [hg1] at hg2
    rw [h1] at hg2
    -- If g divides f, then evaluating f at a root of g should give zero
    -- The roots of X^2 + 3 are ±i√3
    -- Let's evaluate the polynomial at a root
    have h2 : ((X : Polynomial ℤ) ^ 2 + 3 : Polynomial ℤ) ∣ (29 * 37 * X ^ 4 + 2 * X ^ 2 + 9 : Polynomial ℤ) := hg2
    rcases h2 with ⟨h, hh⟩
    -- Now evaluate at X = i√3
    -- We need to show a contradiction
    -- Let's evaluate the polynomial at a root
    have eq1 := congr_arg (fun p : Polynomial ℤ => (p.eval₂ (Int.castRingHom ℂ) (Complex.I * Real.sqrt 3)) ) hh
    simp [pow_two, pow_succ, Complex.ext_iff, mul_add, add_mul, Complex.I_mul_I, mul_assoc, Real.sqrt_nonneg, mul_add, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at eq1
    ring_nf at eq1
    norm_num [Real.sqrt_nonneg, mul_add] at eq1
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 ^ 2), sq_nonneg ((Real.sqrt 3) ^ 2 - 3)]
  constructor
  · -- Show that there's no polynomial g = X + 1 dividing f
    rintro ⟨g, hg1, hg2⟩
    rw [hg1] at hg2
    rw [h1] at hg2
    have h2 : ((X : Polynomial ℤ) + 1 : Polynomial ℤ) ∣ (29 * 37 * X ^ 4 + 2 * X ^ 2 + 9 : Polynomial ℤ) := hg2
    rcases h2 with ⟨h, hh⟩
    -- Now evaluate at x = -1
    have eq1 := congr_arg (fun p : Polynomial ℤ => p.eval (-1 : ℤ)) hh
    simp at eq1
    all_goals nlinarith
  constructor
  · -- Show that there's no polynomial g = X^2 - 3 dividing f
    rintro ⟨g, hg1, hg2⟩
    rw [hg1] at hg2
    rw [h1] at hg2
    have h2 : ((X : Polynomial ℤ) ^ 2 - 3 : Polynomial ℤ) ∣ (29 * 37 * X ^ 4 + 2 * X ^ 2 + 9 : Polynomial ℤ) := hg2
    rcases h2 with ⟨h, hh⟩
    -- Now evaluate at x = sqrt(3)
    have eq1 := congr_arg (fun p : Polynomial ℤ => (p.eval₂ (Int.castRingHom ℝ) (Real.sqrt 3 : ℝ) ) ) hh
    simp [pow_two, pow_succ, Real.sqrt_nonneg, Real.sq_sqrt] at eq1
    ring_nf at eq1
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 ^ 2), sq_nonneg ((Real.sqrt 3) ^ 2 - 3)]
  · -- Show that there's no polynomial g = X^2 - 2X - 3 dividing f
    rintro ⟨g, hg1, hg2⟩
    rw [hg1] at hg2
    rw [h1] at hg2
    -- If g divides f, then evaluating f at a root of g should give zero
    -- The roots of X^2 - 2X - 3 are -1 and 3
    have h2 : ((X : Polynomial ℤ) ^ 2 - 2 * X - 3 : Polynomial ℤ) ∣ (29 * 37 * X ^ 4 + 2 * X ^ 2 + 9 : Polynomial ℤ) := hg2
    rcases h2 with ⟨h, hh⟩
    -- Now evaluate at x = -1
    have eq1 := congr_arg (fun p : Polynomial ℤ => p.eval (-1 : ℤ)) hh
    simp at eq1
    all_goals nlinarith