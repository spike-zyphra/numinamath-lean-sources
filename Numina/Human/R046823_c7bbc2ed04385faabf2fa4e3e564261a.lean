import Mathlib

open Real Set

/- 【Example 2】Prove that in $\triangle A B C$, if $m \geqslant 1$, then
$$
\sin \frac{A}{m}+\sin \frac{B}{m}+\sin \frac{C}{m} \leqslant 3 \sin \frac{\pi}{3 m} \text {, }
$$

equality holds if and only if $A=B=C=\frac{\pi}{3}$. -/
theorem inequalities_255683 (A B C : ℝ) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π)
  (m : ℝ) (hm : m ≥ 1) :
  sin (A / m) + sin (B / m) + sin (C / m) ≤ 3 * sin (π / (3 * m)) ∧
  (sin (A / m) + sin (B / m) + sin (C / m) = 3 * sin (π / (3 * m)) ↔
    (A = π / 3 ∧ B = π / 3 ∧ C = π / 3)) := by
  rcases hA with ⟨hA₁, hA₂⟩
  rcases hB with ⟨hB₁, hB₂⟩
  rcases hC with ⟨hC₁, hC₂⟩
  -- Some preparations
  let t : Finset (Fin 3) := Finset.univ
  let w : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]
  let p : Fin 3 → ℝ := ![A / m, B / m, C / m]
  have h₁ : ∀ i ∈ t, 0 ≤ w i := by
    simp [t, w]
    intro i
    fin_cases i <;> simp
  have h₁' : ∀ i ∈ t, 0 < w i := by
    simp [t, w]
    intro i
    fin_cases i <;> simp
  have h₂ : ∑ i ∈ t, w i = 1 := by
    norm_num [t, w, Finset.sum]
  have h₃ : ∀ i ∈ t, p i ∈ Icc 0 π := by
    simp [t, p]
    intro i
    fin_cases i
    all_goals
      simp
      use by positivity
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  -- Key point: Jensen's inequality
  have H := ConcaveOn.le_map_sum strictConcaveOn_sin_Icc.concaveOn h₁ h₂ h₃
  have h₄ : ∑ i ∈ t, w i • sin (p i) = (sin (A / m) + sin (B / m) + sin (C / m)) / 3 := by
    simp [t, w, p, Finset.sum]
    cancel_denoms
    ac_rfl
  have h₅ : ∑ i ∈ t, w i • p i = π / (3 * m) := by
    simp [t, w, p, Finset.sum, ← hABC]
    ring
  rw [h₄, h₅] at H
  cancel_denoms at H
  use H
  calc sin (A / m) + sin (B / m) + sin (C / m) = 3 * sin (π / (3 * m))
    _ ↔ sin (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • sin (p i) := by
      rw [h₄, h₅]
      constructor <;> intro h
      . linarith only [h]
      . linarith only [h]
    _ ↔ ∀ j ∈ t, p j = π / (3 * m) := h₅ ▸ StrictConcaveOn.map_sum_eq_iff strictConcaveOn_sin_Icc h₁' h₂ h₃ -- The equality condition of Jensen's inequality for strict concave functions
    _ ↔ A / m = π / (3 * m) ∧ B / m = π / (3 * m) ∧ C / m = π / (3 * m) := by
      simp [t, p, Fin.forall_fin_succ]
    _ ↔ A = π / 3 ∧ B = π / 3 ∧ C = π / 3 := by
      congrm ?_ ∧ ?_ ∧ ?_
      all_goals
        constructor <;> intro h
        . field_simp at h
          nlinarith only [h, hm]
        . field_simp
          linear_combination h * 3 * m
