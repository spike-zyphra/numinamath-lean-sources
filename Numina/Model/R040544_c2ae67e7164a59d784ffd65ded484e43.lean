import Mathlib

open Polynomial

theorem number_theory_84401 (f : ℤ[X]) (hf : f.natDegree = 2 ∧ ∀ k : ℤ, 5 ∣ f.eval k) :
    ∀ i ≤ f.natDegree, 5 ∣ f.coeff i := by
  rcases hf with ⟨hf_degree, hf5⟩
  have h7 : f.eval 0 % 5 = 0 := by
    specialize hf5 0
    omega
  have h71 : f.eval 1 % 5 = 0 := by
    specialize hf5 1
    omega
  have h72 : f.eval 2 % 5 = 0 := by
    specialize hf5 2
    omega
  have h73 : f.eval 3 % 5 = 0 := by
    specialize hf5 3
    omega
  have h74 : f.eval 4 % 5 = 0 := by
    specialize hf5 4
    omega
  have h75 : f.eval 5 % 5 = 0 := by
    specialize hf5 5
    omega
  have eq1 : f.eval 0 = f.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, hf_degree, Finset.sum_range_succ]
    all_goals ring
  have eq2 : f.eval 1 = f.coeff 0 + f.coeff 1 + f.coeff 2 := by
    simp [Polynomial.eval_eq_sum_range, hf_degree, Finset.sum_range_succ]
    all_goals ring
  have eq3 : f.eval 2 = f.coeff 0 + 2 * f.coeff 1 + 4 * f.coeff 2 := by
    simp [Polynomial.eval_eq_sum_range, hf_degree, Finset.sum_range_succ]
    all_goals ring
  have eq4 : f.eval 3 = f.coeff 0 + 3 * f.coeff 1 + 9 * f.coeff 2 := by
    simp [Polynomial.eval_eq_sum_range, hf_degree, Finset.sum_range_succ]
    all_goals ring
  have eq5 : f.eval 4 = f.coeff 0 + 4 * f.coeff 1 + 16 * f.coeff 2 := by
    simp [Polynomial.eval_eq_sum_range, hf_degree, Finset.sum_range_succ]
    all_goals ring
  have eq6 : f.eval 5 = f.coeff 0 + 5 * f.coeff 1 + 25 * f.coeff 2 := by
    simp [Polynomial.eval_eq_sum_range, hf_degree, Finset.sum_range_succ]
    all_goals ring
  intro i hi
  have h9 : i = 0 ∨ i = 1 ∨ i = 2 := by
    have h10 : i ≤ 2 := by
      have h11 : f.natDegree = 2 := hf_degree
      have h12 : i ≤ f.natDegree := by linarith
      rw [h11] at h12
      linarith
    have : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    assumption
  rcases h9 with (rfl | rfl | rfl)
  · -- i = 0
    have h1 : 5 ∣ f.coeff 0 := by
      omega
    assumption
  · -- i = 1
    have h2 : 5 ∣ f.coeff 1 := by
      omega
    assumption
  · -- i = 2
    have h3 : 5 ∣ f.coeff 2 := by
      omega
    assumption