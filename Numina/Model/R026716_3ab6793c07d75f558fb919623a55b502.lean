import Mathlib

open Set Real

theorem algebra_108250 {a : ℝ} (ha : -2 ≤ a) :
    {z | ∃ x, -2 ≤ x ∧ x ≤ a ∧ z = x ^ 2} ⊆ {y | ∃ x, -2 ≤ x ∧ x ≤ a ∧ y = 2 * x + 3} ↔
    1 / 2 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- (→) If $C \subseteq B$, then $\frac{1}{2} \leq a \leq 3$
    intro h
    have h1 : 1 / 2 ≤ a := by
      have h4 : (4 : ℝ) ∈ {z | ∃ x, -2 ≤ x ∧ x ≤ a ∧ z = x ^ 2} := by
        use -2
        constructor
        · nlinarith
        constructor
        · nlinarith
        · norm_num
      have h4' : (4 : ℝ) ∈ {y | ∃ x, -2 ≤ x ∧ x ≤ a ∧ y = 2 * x + 3} := h h4
      rcases h4' with ⟨x, hx1, hx2, h4x⟩
      have hx3 : 2 * x + 3 = 4 := by linarith [h4x]
      have hx4 : x = 1 / 2 := by linarith [hx3]
      have hx5 : x ≤ a := hx2
      rw [hx4] at hx5
      linarith [hx5]
    have h2 : a ≤ 3 := by
      have ha2 : a ^ 2 ∈ {z | ∃ x, -2 ≤ x ∧ x ≤ a ∧ z = x ^ 2} := by
        use a
        all_goals
          nlinarith
      have ha2' : a ^ 2 ∈ {y | ∃ x, -2 ≤ x ∧ x ≤ a ∧ y = 2 * x + 3} := h ha2
      rcases ha2' with ⟨x, hx1, hx2, h0⟩
      have h1 : 2 * x + 3 = a ^ 2 := by linarith [h0]
      have hx2 : x ≤ a := by linarith
      nlinarith [sq_nonneg (a - 3), sq_nonneg (x - a), sq_nonneg (a - 3)]
    exact ⟨h1, h2⟩
  · -- (←) If $\frac{1}{2}\leq a \leq 3$, then $C\subseteq B$
    rintro ⟨ha1, ha2⟩
    intro z hz
    rcases hz with ⟨x, hx1, hx2, hz⟩
    use ( (x) ^ 2 - 3 ) / 2
    constructor
    · -- Show -2 ≤ (x ^ 2 - 3)/2
      nlinarith [sq_nonneg x, sq_nonneg (x - a), sq_nonneg (x + 2), sq_nonneg (a - 3), sq_nonneg (a - 1 / 2), sq_nonneg (x - (-2)), sq_nonneg (x - a)]
    constructor
    · -- Show ((x) ^ 2 - 3)/2 ≤ a
      nlinarith [sq_nonneg (x - a), sq_nonneg (x + 2), sq_nonneg (a - 3), sq_nonneg (a - 1 / 2), sq_nonneg (x - (-2)), sq_nonneg (x - a), sq_nonneg (a - x)]
    · -- Show z = 2 * ((x) ^ 2 - 3)/2 + 3
      linarith [hz]