import Mathlib

theorem algebra_20505 (f : ℝ → ℝ) (hf : f = fun x => x ^ 5 - x ^ 4 - 72 * x ^ 3) :
    Set.ncard {x | f x = 0} = 3 := by

  have eq1 : ∀ x : ℝ, f x = x ^ 5 - x ^ 4 - 72 * x ^ 3 := by
    intro x
    rw [hf]

  have h1 : {x : ℝ | f x = 0} = { -8, 0, 9 } := by
    ext x
    simp [eq1]
    constructor
    · -- Assume f x = 0; prove x ∈ { -8, 0, 9 }
      intro h_eq
      have h_eq2 : x ^ 5 - x ^ 4 - 72 * x ^ 3 = 0 := by
        nlinarith
      have h_eq3 : x ^ 3 * (x ^ 2 - x - 72) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h_eq3) with h3 h4
      · -- Case where $x^3 = 0$, so $x = 0$
        have h_eq5 : x = 0 := by
          have h_eq8 : x ^ 3 = 0 := by
            nlinarith
          have h_eq9 : x ^ 3 = 0 := h_eq8
          have h_eq10 : x = 0 := by
            have h_eq11 : x ^ 3 = 0 := h_eq9
            have h_eq12 : x * (x * x) = 0 := by
              ring_nf
              nlinarith
            cases (mul_eq_zero.mp h_eq12) with
            | inl h_eq13 =>
              exact h_eq13
            | inr h_eq14 =>
              have h_eq15 : x * x = 0 := by
                linarith
              have h_eq16 : x = 0 := by
                have h_eq17 : x ^ 2 = 0 := by
                  nlinarith
                have h_eq18 : x = 0 := by
                  nlinarith
                exact h_eq18
              exact h_eq16
          exact h_eq10
        right
        left
        exact h_eq5
      · -- Solve $x^2 - x - 72 = 0$
        have h_eq4 : x ^ 2 - x - 72 = 0 := by
          nlinarith
        have h_eq6 : (x - 9) * (x + 8) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h_eq6) with h7 h8
        · -- Case 9
          right
          right
          linarith
        · -- Case -8
          left
          nlinarith
    · -- Assume x ∈ { -8, 0, 9 }, prove f x = 0
      rintro (rfl | rfl | rfl)
      · -- f (-8) = 0
        norm_num
      · -- f 0 = 0
        norm_num
      · -- f 9 = 0
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { norm_num }