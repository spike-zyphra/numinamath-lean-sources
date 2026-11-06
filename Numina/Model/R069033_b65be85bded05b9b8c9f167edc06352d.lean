import Mathlib

theorem algebra_292769 (x : Fin 5 → ℝ) (h : |x 1 - x 0| = 2 * |x 2 - x 1| ∧ 2 * |x 2 - x 1| = 3 * |x 3 - x 2| ∧ 3 * |x 3 - x 2| = 4 * |x 4 - x 3| ∧ 4 * |x 4 - x 3| = 5 * |x 0 - x 4|) :
    ∃ c, ∀ i, x i = c := by
  rcases h with ⟨h1, h2, h3, h4⟩
  cases' abs_cases (x 1 - x 0) with h10 h10 <;> cases' abs_cases (x 2 - x 1) with h21 h21 <;> cases' abs_cases (x 3 - x 2) with h32 h32 <;> cases' abs_cases (x 4 - x 3) with h43 h43 <;> cases' abs_cases (x 0 - x 4) with h04 h04
  all_goals
    have h11 : x 0 = x 1 := by linarith
    have h22 : x 1 = x 2 := by linarith
    have h33 : x 2 = x 3 := by linarith
    have h44 : x 3 = x 4 := by linarith
    have h00 : x 0 = x 4 := by linarith
    refine' ⟨x 0, fun i => by fin_cases i <;> simp [h11, h22, h33, h44, h00]⟩