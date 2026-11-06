import Mathlib

open Polynomial

theorem algebra_232473 {a : ℝ}
    (x₁ x₂ x₃ : ℝ) (hroots : (X ^ 3 - 3 * X ^ 2 + C a * X + 3 : ℝ[X]).roots = {x₁, x₂, x₃}) (hseq : ∃ d > 0, x₂ = x₁ + d ∧ x₃ = x₂ + d) :
    a = -1 ∧ x₁ = -1 ∧ x₂ = 1 ∧ x₃ = 3 := by
  set p : ℝ[X] := X ^ 3 - 3 * X ^ 2 + C a * X + 3 with hp
  have hdeg : p.natDegree = 3 := by
    rw [hp]
    compute_degree!
  have hcard : p.roots.card = p.natDegree := by
    rw [hp, hroots]
    simp [← hp, hdeg]
  have hcoeff : p.leadingCoeff = 1 := by
    rw [hp, ← Polynomial.coeff_natDegree, hdeg]
    simp
  have h₀ := Polynomial.coeff_eq_esymm_roots_of_card hcard (k := 0) (by simp [hdeg])
  have h₁ := Polynomial.coeff_eq_esymm_roots_of_card hcard (k := 1) (by simp [hdeg])
  have h₂ := Polynomial.coeff_eq_esymm_roots_of_card hcard (k := 2) (by simp [hdeg])
  simp [hcoeff, hdeg, hroots, Multiset.esymm, Multiset.powersetCard_one] at h₀ h₁ h₂
  simp [hp] at h₀ h₁ h₂
  rcases hseq with ⟨d, hd, hseq₁, hseq₂⟩
  replace hseq₁ : x₁ = x₂ - d := eq_sub_of_add_eq hseq₁.symm
  rw [hseq₁, hseq₂] at h₀ h₁ h₂ ⊢
  ring_nf at h₀ h₁ h₂ ⊢
  obtain rfl : x₂ = 1 := by linarith only [h₂]
  obtain rfl : d = 2 := by nlinarith only [h₀, hd]
  subst h₁
  norm_num
