import Mathlib

-- Define the condition.
def condition (x : Fin 4 → ℝ) (k : ℝ) : Prop :=
  let A := x 0 + x 1
  let B := x 2 + x 3
  let C := x 0 + x 2
  let D := x 1 + x 3
  let E := x 0 + x 3
  let F := x 1 + x 2
  A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ D ≠ 0 ∧ E ≠ 0 ∧ F ≠ 0 ∧
  A / B = k ∧ B / A = k ∧
  C / D = k ∧ D / C = k ∧
  E / F = k ∧ F / E = k ∧
  ¬(x 0 = x 1 ∧ x 1 = x 2 ∧ x 2 = x 3)

/-Problem 5. There are 4 numbers, not all of which are the same. If you take any two of them, the ratio of the sum of these two numbers to the sum of the other two numbers will be the same value $\mathrm{k}$. Find the value of $\mathrm{k}$. Provide at least one set of four numbers that satisfy the condition. Describe all possible sets of such numbers and determine how many there are.-/
theorem algebra_200444 : ∀ k, (∃ x : Fin 4 → ℝ, condition x k) → k = -1 := by
  intros k h
  obtain ⟨x, h_cond⟩ := h
  rcases h_cond with ⟨h_A_ne_0, h_B_ne_0, h_C_ne_0, h_D_ne_0, h_E_ne_0, h_F_ne_0, h_AB_k, h_BA_k, h_CD_k, h_DC_k, h_EF_k, h_FE_k, h_not_all_eq⟩
  let A := x 0 + x 1
  let B := x 2 + x 3
  -- Derive $k$ euqals $±1$ from $A/B = B/A = k$.
  have h_AB : A ≠ 0 ∧ B ≠ 0 := by
    exact ⟨h_A_ne_0, h_B_ne_0⟩
  have h_k : k = 1 ∨ k = -1 := by
    have h_k_square : k * k = 1 := by
      have : (A / B) * (B / A) = 1 := by
        field_simp [h_AB.1, h_AB.2]
      rw [h_AB_k, h_BA_k] at this
      exact this
    have : k^2 = 1 := by
      simp [sq, h_k_square]
    exact sq_eq_one_iff.mp this
  -- Rule out $k = 1$.
  have h_not_k1 : k ≠ 1 := by
    intro h_k1
    rw [h_k1] at h_AB_k h_CD_k h_EF_k
    have h_eq : x 0 + x 1 = x 2 + x 3 ∧ x 0 + x 2 = x 1 + x 3 ∧ x 0 + x 3 = x 1 + x 2 := by
      have h_D_ne_0 : x 1 + x 3 ≠ 0 := h_D_ne_0
      have h_F_ne_0 : x 1 + x 2 ≠ 0 := h_F_ne_0
      exact ⟨(div_eq_one_iff_eq h_AB.2).mp h_AB_k,
             (div_eq_one_iff_eq h_D_ne_0).mp h_CD_k,
             (div_eq_one_iff_eq h_F_ne_0).mp h_EF_k⟩
    -- Derive that all four numbers are equal, contradicting the condition.
    have h_all_eq : x 0 = x 1 ∧ x 1 = x 2 ∧ x 2 = x 3 := by
      have h1 : x 0 + x 1 = x 2 + x 3 := h_eq.1
      have h2 : x 0 + x 2 = x 1 + x 3 := h_eq.2.1
      have h3 : x 0 + x 3 = x 1 + x 2 := h_eq.2.2
      have h_x0_x1 : x 0 = x 1 := by nlinarith
      have h_x1_x2 : x 1 = x 2 := by nlinarith
      have h_x2_x3 : x 2 = x 3 := by nlinarith
      exact ⟨h_x0_x1, h_x1_x2, h_x2_x3⟩
    have h_contradict : ¬ (x 0 = x 1 ∧ x 1 = x 2 ∧ x 2 = x 3) := h_not_all_eq
    contradiction
  -- Verify $k = -1$.
  have h_k_minus_one : k = -1 := by
    cases h_k with
    | inl h => contradiction
    | inr h => exact h
  exact h_k_minus_one
