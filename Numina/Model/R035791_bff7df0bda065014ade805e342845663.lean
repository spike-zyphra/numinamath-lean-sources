import Mathlib

open Polynomial

theorem algebra_221516 {p q : ℝ}
    (h₁ : ∃ x₁ x₂ : ℤ, (X ^ 2 + C p * X + C q : ℝ[X]).roots = {↑x₁, ↑x₂})
    (h₂ : ∃ y₁ y₂ : ℤ, (X ^ 2 + C p * X - C q : ℝ[X]).roots = {↑y₁, ↑y₂}) :
    ∃ a b : ℤ, p ^ 2 = a ^ 2 + b ^ 2 := by
  simp only [sub_eq_add_neg] at h₂
  rcases h₁ with ⟨x₁, x₂, hx₁⟩
  rcases h₂ with ⟨y₁, y₂, hy₂⟩

  have h₁ : X ^ 2 + C p * X + C q = (X - (x₁ : ℝ[X])) * (X - (x₂ : ℝ[X])) := by
    calc _
    _ = C 1 * X ^ 2 + C p * X + C q := by simp
    _ = Multiset.prod (.map (fun x ↦ X - C x) (C 1 * X ^ 2 + C p * X + C q).roots) := by
      symm
      refine prod_multiset_X_sub_C_of_monic_of_roots_card_eq ?_ ?_
      · exact leadingCoeff_quadratic one_ne_zero
      · rw [natDegree_quadratic one_ne_zero]
        simp [hx₁]
    _ = _ := by simp [hx₁]
  have h₂ : X ^ 2 + C p * X - C q = (X - (y₁ : ℝ[X])) * (X - (y₂ : ℝ[X])) := by
    calc _
    _ = C 1 * X ^ 2 + C p * X + C (-q) := by simp [sub_eq_add_neg]
    _ = Multiset.prod (.map (fun x ↦ X - C x) (C 1 * X ^ 2 + C p * X + C (-q)).roots) := by
      symm
      refine prod_multiset_X_sub_C_of_monic_of_roots_card_eq ?_ ?_
      · exact leadingCoeff_quadratic one_ne_zero
      · rw [natDegree_quadratic one_ne_zero]
        simp [hy₂]
    _ = _ := by simp [hy₂]

  have ⟨hp₁, hq₁⟩ : p = ↑(-(x₁ + x₂)) ∧ q = ↑(x₁ * x₂) := by
    suffices X ^ 2 + C p * X + C q = X ^ 2 + C (-(x₁ + x₂ : ℝ)) * X + C (x₁ * x₂ : ℝ) by
      refine ⟨?_, ?_⟩
      · simpa [-map_intCast] using ext_iff.mp this 1
      · simpa [-map_intCast] using ext_iff.mp this 0
    rw [h₁]
    simp only [map_add, map_neg, map_intCast, map_mul]
    ring
  have ⟨hp₂, hq₂⟩ : p = ↑(-(y₁ + y₂)) ∧ q = ↑(-(y₁ * y₂)) := by
    suffices X ^ 2 + C p * X - C q = X ^ 2 + C (-(y₁ + y₂ : ℝ)) * X + C (y₁ * y₂ : ℝ) by
      refine ⟨?_, ?_⟩
      · simpa [-map_intCast] using ext_iff.mp this 1
      · rw [← neg_inj]
        simpa [-map_intCast] using ext_iff.mp this 0
    rw [h₂]
    simp only [map_add, map_neg, map_intCast, map_mul]
    ring
  obtain ⟨p', hp'⟩ : ∃ p' : ℤ, p = p' := ⟨_, hp₁⟩
  obtain ⟨q', hq'⟩ : ∃ q' : ℤ, q = q' := ⟨_, hq₁⟩
  have hp₁ : p' = -(x₁ + x₂) := Int.cast_inj.mp (hp' ▸ hp₁)
  have hp₂ : p' = -(y₁ + y₂) := Int.cast_inj.mp (hp' ▸ hp₂)
  have hq₁ : q' = x₁ * x₂ := Int.cast_inj.mp (hq' ▸ hq₁)
  have hq₂ : q' = -(y₁ * y₂) := Int.cast_inj.mp (hq' ▸ hq₂)

  have hpm : p' ^ 2 - 4 * q' = (x₁ - x₂) ^ 2 := by
    rw [hp₁, hq₁]
    ring
  have hpn : p' ^ 2 + 4 * q' = (y₁ - y₂) ^ 2 := by
    rw [hp₂, hq₂]
    ring

  use p'
  use (0 : ℤ)
  have hp_eq : p = (p' : ℝ) := by simpa using hp'
  rw [hp_eq]
  simp [pow_two]