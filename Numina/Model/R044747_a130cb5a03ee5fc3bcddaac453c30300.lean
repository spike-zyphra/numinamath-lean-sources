import Mathlib

open Finset Real Nat
theorem number_theory_241506 {j m : ℤ} (ineq : j > m) (hjm : m = 10 * (j % 10) + (j / 10)) (hj: 0 ≤ j) (hm: 0 ≤ m) (hj2: j ≤ 99) (hm2: m ≤ 99)
    (hdiff : ∃ k, k^2 = j^2 - m^2) :
    j = 65 ∧ m = 56 := by
  rcases hdiff with ⟨k, hk⟩
  have h1 : j ≤ 99 := by linarith
  have h2 : j ≥ 0 := by linarith
  have h3 : m ≤ 99 := by linarith
  have h4 : m ≥ 0 := by linarith
  interval_cases j <;> norm_num [hjm] at *
  <;> try { 
    have h5 : k ≤ 99 := by nlinarith
    have h6 : k ≥ -99 := by nlinarith
    interval_cases k <;> omega 
  }
  <;> omega