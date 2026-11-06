import Mathlib

theorem algebra_294898 {a b c x1 x2 : ℤ} (ha : a ≠ 0) (hroots : x1 ≠ x2)
    (h : ∃ n, a = n ∧ b = n + 1 ∧ c = n + 2 ∧ x1 = n + 3 ∧ x2 = n + 4) :
    (a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0) ↔
    (a = 2 ∧ b = -2 ∧ c = 0) ∨ (a = -2 ∧ b = 2 ∧ c = 0) := by
  constructor
  · -- Forward direction: assume the equations and prove the specific forms
    intro h_eq
    rcases h with ⟨n, ha_eq, hb_eq, hc_eq, hx1_eq, hx2_eq⟩
    rw [ha_eq, hb_eq, hc_eq, hx1_eq, hx2_eq] at h_eq
    rcases h_eq with ⟨h1, h2⟩
    have eq1 := h1
    have eq2 := h2
    nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n + 3), sq_nonneg (n + 4), sq_nonneg (n + 2), sq_nonneg (n + 1)]
  · -- Backward direction: prove that the specific forms satisfy the equations
    rintro (h | h)
    · -- Case 1: a = 2, b = -2, c = 0
      rcases h with ⟨ha_eq, hb_eq, hc_eq⟩
      -- We need to prove that:
      -- 2 * x1^2 + (-2) * x1 + 0 = 0
      -- 2 * x2^2 + (-2) * x2 + 0 = 0
      -- With x1 and x2 being consecutive integers not equal to each other
      -- The roots of 2x^2 - 2 = 0 are x = ±1
      -- So x1 and x2 must be 1 and -1 in some order
      -- But then a, b, c, x1, x2 would be 2, -2, 0, 1, -1
      -- These are five consecutive integers: -2, -1, 0, 1, 2 but not in the specific order
      -- Lean's hypothesis requires a different order
      -- To make it fit the Lean hypothesis, we need to find n such that:
      -- a = n, b = n + 1, c = n + 2, x1 = n + 3, x2 = n + 4
      -- But a = 2, b = -2, so:
      -- 2 = n and -2 = n + 1 → n = -3 and n = 2, contradiction
      -- Therefore, it's impossible to satisfy the Lean's specific ordering
      -- The Lean proof shows this contradiction
      refine ⟨by omega, by omega⟩
    · -- Case 2: a = -2, b = 2, c = 0
      rcases h with ⟨ha_eq, hb_eq, hc_eq⟩
      -- Similarly, the equation is -2x^2 + 2 = 0 with roots ±1
      -- a = -2, b = 2, c = 0, x1 and x2 = ±1
      -- These numbers: -2, 2, 0, 1, -1 are -2, -1, 0, 1, 2 sorted
      -- To fit Lean's order: a = n, b = n + 1, etc.
      -- a = -2 = n
      -- b = 2 = n + 1 → n = 1, but a = n = -2, contradiction
      -- Lean's proof shows this contradiction
      refine ⟨by omega, by omega⟩
      