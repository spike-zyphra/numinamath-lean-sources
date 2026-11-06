import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_283639 {S : Set ℂ} (hS : S = {z | ∃ r : ℝ, (3 + 4 * I) * z = r}) :
    ∃ m c : ℝ, ∀ z ∈ S, z.re = m * z.im + c := by 
  use (-3 / 4), (0)
  intro z hz
  rw [hS] at hz
  rcases hz with ⟨r, hr⟩
  have eq1 := congr_arg Complex.re hr
  have eq2 := congr_arg Complex.im hr
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2
  ring_nf at eq1 eq2
  -- extract eq2 solving about real part re , solve the equation apply linarith
  linarith