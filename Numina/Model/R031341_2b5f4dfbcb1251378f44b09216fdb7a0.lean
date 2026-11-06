import Mathlib

theorem algebra_142944 {a : ℝ} (ha : a ≠ 1) :
    (∃! x : ℝ, (a - 1) * x ^ 2 + a * x - 1 = x - 2) ↔ a = 5 := by
  constructor
  · -- (∃! x : ℝ, (a - 1) * x ^ 2 + a * x - 1 = x - 2) → a = 5
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h1 : (a - 1) * x ^ 2 + a * x - 1 = x - 2 := hx1
    have h2 : (a - 1) * x ^ 2 + (a - 1) * x + 1 = 0 := by
      nlinarith
    have eq1 := hx2 (-1 - x) (by
      nlinarith [h2]
    )
    have eq2 : -1 - x = x := by 
      nlinarith
    have eq3 : x = -1 / 2 := by 
      nlinarith
    rw [eq3] at h2
    nlinarith
  · -- a = 5 → (∃! x : ℝ, (a - 1) * x ^ 2 + a * x - 1 = x - 2)
    intro ha_eq
    use -1 / 2
    constructor
    · -- Show that -1/2 is a solution
      rw [ha_eq]
      norm_num
    · -- Show that it's unique
      intro y hy
      rw [ha_eq] at *
      have h_eq : 4 * y ^ 2 + 4 * y + 1 = 0 := by
        nlinarith
      have h_eq2 : (2 * y + 1) ^ 2 = 0 := by
        nlinarith
      have h_eq3 : 2 * y + 1 = 0 := by
        apply pow_eq_zero 
        exact h_eq2
      have h_eq4 : y = -1 / 2 := by
        linarith
      exact h_eq4