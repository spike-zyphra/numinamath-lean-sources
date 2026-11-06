import Mathlib

open Real

/-
3. In the Cartesian coordinate system, points whose both coordinates are rational numbers are called rational points. If $a$ is an irrational number, then among all lines passing through the point $(a, 0)$,
(A) there are infinitely many lines, each of which contains at least two rational points
(B) there are exactly $n(2 \leqslant n<+\infty)$ lines, each of which contains at least two rational points
(C) there is exactly one line that passes through at least two rational points
(D) each line passes through at most one rational point
 -/
namespace number_theory_197352

def straightLineOf a b c := {⟨x, y⟩ : ℝ × ℝ | (a ≠ 0 ∨ b ≠ 0) ∧ a * x + b * y + c = 0}

instance : Coe (ℚ × ℚ) (ℝ × ℝ) where
  coe := fun (x, y) => (x, y)

theorem number_theory_197352 (a' : ℝ) (ha' : Irrational a') :
    {l | ∃ a b c : ℝ, l = straightLineOf a b c ∧
    ⟨a', 0⟩ ∈ l ∧
    ∃ p₁ p₂ : ℚ × ℚ, p₁ ≠ p₂ ∧ (p₁ : ℝ × ℝ) ∈ l ∧ (p₂ : ℝ × ℝ) ∈ l}.ncard
    = 1 := by
  have : {l | ∃ a b c : ℝ, l = straightLineOf a b c ∧
      ⟨a', 0⟩ ∈ l ∧
      ∃ p₁ p₂ : ℚ × ℚ, p₁ ≠ p₂ ∧ (p₁ : ℝ × ℝ) ∈ l ∧ (p₂ : ℝ × ℝ) ∈ l} =
      {{x | x.2 = 0}} := by
    ext l
    simp
    constructor
    . simp
      simp [straightLineOf]
      rintro a b c rfl ⟨a_ne_0_or_b_ne_0, point_a'_0_in_l⟩ x₁ y₁ x₂ y₂ p₁_ne_p₂ ⟨_, p₁_in_l⟩ ⟨_, p₂_in_l⟩
      simp at point_a'_0_in_l p₁_in_l p₂_in_l
      by_cases w_b_eq_0 : b = 0
      . subst w_b_eq_0
        simp at a_ne_0_or_b_ne_0
        simp at p₁_in_l p₂_in_l
        have x₁_eq : x₁ = a' := by
          have : a * (x₁ - a') = 0 := by
            linarith
          --nlinarith
          simp [a_ne_0_or_b_ne_0] at this
          linarith
        exfalso
        have : Irrational x₁ := by
          rw [x₁_eq]
          exact ha'
        simp [Irrational] at this
      . simp [w_b_eq_0]
        let k := - a / b
        by_cases w_k_eq_0 : k = 0
        . have : a = 0 := by
            unfold k at w_k_eq_0
            field_simp at w_k_eq_0
            exact w_k_eq_0
          subst this
          have : c = 0 := by
            simp at point_a'_0_in_l
            exact point_a'_0_in_l
          subst this
          simp [w_b_eq_0]
        . exfalso
          let k' := (y₁ - y₂) / (x₁ - x₂)
          have : x₁ - x₂ ≠ 0 := by
            intro x₁_sub_x₂_eq_0
            have x₁_eq_x₂ : x₁ = x₂ := by
              linarith
            have : y₁ = y₂ := by
              have : b * (y₁ - y₂) = 0 := by
                --rify at x₁_eq_x₂
                have : a * x₁ + b * y₁ = a * x₂ + b * y₂ := by
                  linarith
                rw [x₁_eq_x₂] at this -- don't know why this is needed explicitly
                linarith
              simp [w_b_eq_0] at this
              rify
              linarith
            exact p₁_ne_p₂ x₁_eq_x₂ this
          rify at this
          have k_eq_k' : k = k' := by
            unfold k k'
            push_cast
            field_simp
            linarith
          have : y₁ = k' * (x₁ - a') := by
            rw [←k_eq_k']
            unfold k
            field_simp
            linarith
          have : k' ≠ 0 := by
            rify
            rw [←k_eq_k']
            exact w_k_eq_0
          have : a' = x₁ - y₁ / k' := by
            field_simp
            linarith
          have : Irrational (x₁ - y₁ / k') := by
            rw [←this]
            exact ha'
          simp at this
    . rintro rfl
      simp
      constructor
      . use 0, 1, 0
        ext ⟨x, y⟩
        unfold straightLineOf
        simp
      . exact exists_pair_ne ℚ
  rw [this]
  simp

end number_theory_197352
open number_theory_197352
