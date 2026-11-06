import Mathlib

open Polynomial

/- Let $p(x)$ be a monic polynomial of degree 4, such that $p(1) = 17,$ $p(2) = 34,$ and $p(3) = 51.$  Find $p(0) + p(4).$ -/
theorem algebra_13755 {p : ℝ[X]} (hp : p.Monic) (h₀ : p.natDegree = 4) (h₁ : p.eval 1 = 17) (h₂ : p.eval 2 = 34) (h₃ : p.eval 3 = 51) :
    p.eval 0 + p.eval 4 = 92 := by
  set q := p - 17 * X with hq
  have hqdeg : q.natDegree = 4 := by
    rw [hq, natDegree_sub_eq_left_of_natDegree_lt (by simp [h₀]), h₀]
  have hqmonic : q.Monic := by
    refine Monic.sub_of_left hp ?_
    rw [(degree_eq_iff_natDegree_eq (Monic.ne_zero hp)).mpr h₀]
    suffices H : (17 * X : ℝ[X]).degree = 1 by simp [H]
    compute_degree!
  have hqne0 : q ≠ 0 := Monic.ne_zero hqmonic
  have hqroots : {1, 2, 3} ⊆ q.roots := by
    simp [hqne0]
    norm_num [hq, h₁, h₂, h₃]
  have hp₁ : p = q + 17 * X := (sub_add_cancel p (17 * X)).symm
  rw [hp₁]
  clear_value q
  clear p hp h₀ h₁ h₂ h₃ hq hp₁
  rw [← Multiset.le_iff_subset (by norm_num),
      ← Multiset.prod_X_sub_C_dvd_iff_le_roots hqne0] at hqroots
  rcases hqroots with ⟨s, hs⟩
  have hslin : s.natDegree = 1 := by
    have hs' : q.natDegree = ((Multiset.map (fun a ↦ X - C a) {1, 2, 3}).prod * s).natDegree := by rw [hs]
    have ⟨k₁, k₂⟩ : (Multiset.map (fun a ↦ (X - C a : ℝ[X])) {1, 2, 3}).prod ≠ 0 ∧ s ≠ 0 := by
      refine ne_zero_and_ne_zero_of_mul ?_
      rwa [← hs]
    rw [natDegree_mul k₁ k₂, natDegree_multiset_prod_X_sub_C_eq_card] at hs'
    simp [hqdeg] at hs'
    linarith only [hs']
  have hsmonic : s.Monic := by
    refine Monic.of_mul_monic_left (p := (Multiset.map (fun a ↦ X - C a) {1, 2, 3}).prod) ?_ ?_
    . refine monic_multiset_prod_of_monic _ _ ?_
      intro i hi
      exact monic_X_sub_C i
    . rwa [← hs]
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, s = X + C r := ⟨s.coeff 0, Monic.eq_X_add_C hsmonic hslin⟩
  simp [hs]
  ring
