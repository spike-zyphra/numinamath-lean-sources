import Mathlib

open Real

theorem inequalities_42383 {p : ℝ → ℝ} (hp : ∃ a b c, p = fun x => a * x ^ 2 + b * x + c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 1) :
    ∀ x : Finset ℝ, (∀ i ∈ x, 0 < i) ∧ ∏ i ∈ x, i = 1 → ∏ i ∈ x, p i ≥ 1 := by 
  rcases hp with ⟨a, b, c, hp_eq⟩
  intro x h
  rcases h with ⟨hx_pos, h_eq⟩
  have h4 : (∏ i in x, p i) ≥ (∏ i in x, (i : ℝ)) := by
    apply Finset.prod_le_prod
    · 
      intro i hi
      have hp_pos : 0 < i := by
        specialize hx_pos i (show i ∈ x by exact hi)
        linarith 
      have h_eq3 : p i ≥ i := by 
        have h8 : p i = a * (i) ^ 2 + b * (i) + c := by
          rw [hp_eq] 
        rw [h8] 
        -- We need show p i >= i for i > 0
        -- equals to showing a * (i)^2 + b * i + c >= i
        -- equals to showing a * (i)^2 + (b - 1) * i + c >= 0
        nlinarith [sq_nonneg (i - 1), sq_nonneg (a * (i) + (b - 1) / 2), sq_nonneg (c * i - c / 2), sq_nonneg (a * i - c * (i ^ 2)), sq_nonneg (i ^ 2 - 1 / i ^ 2), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (i * (a * (i) + (b - 1) / 2)), sq_nonneg (a * i - (b - 1) / 2 * i), hsum]
      nlinarith 
    · 
      intro i hi
      have hp_pos : 0 < i := by
        specialize hx_pos i (show i ∈ x by exact hi)
        linarith 
      have h_eq3 : p i ≥ i := by 
        have h8 : p i = a * (i) ^ 2 + b * (i) + c := by
          rw [hp_eq] 
        rw [h8] 
        -- We need show p i >= i for i > 0
        -- equals to showing a * (i)^2 + b * i + c >= i
        -- equals to showing a * (i)^2 + (b - 1) * i + c >= 0
        nlinarith [sq_nonneg (i - 1), sq_nonneg (a * (i) + (b - 1) / 2), sq_nonneg (c * i - c / 2), sq_nonneg (a * i - c * (i ^ 2)), sq_nonneg (i ^ 2 - 1 / i ^ 2), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (i * (a * (i) + (b - 1) / 2)), sq_nonneg (a * i - (b - 1) / 2 * i), hsum]
      nlinarith
  have h7 : (∏ i in x, (i : ℝ)) = 1 := by 
    linarith [h_eq] 
  have h8 : (∏ i in x, p i) ≥ 1 := by 
    nlinarith [h4, h7] 
  exact h8