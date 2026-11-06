import Mathlib

def isSquareFriendly (c : ℤ) : Prop := ∀ m, IsSquare (m^2 + 18 * m + c)

theorem algebra_260073 :
    ∃! c, isSquareFriendly c := by
  use 81
  constructor
  · -- Show that 81 is square-friendly
    show isSquareFriendly 81
    intro m
    have h1 : IsSquare (m^2 + 18 * m + 81) := by
      use m + 9
      ring
    exact h1
  · -- Show that if c is square-friendly, then c = 81
    intro c h
    have h1 := h (-9)
    rcases h1 with ⟨k, hk⟩
    have eq1 : c = 81 + k^2 := by
      nlinarith
    have h2 := h (-8)
    rcases h2 with ⟨k2, hk2⟩
    have h_eq1 : 1 + k^2 = k2^2 := by
      nlinarith [eq1]
    have h3 := h (-7)
    rcases h3 with ⟨k3, hk3⟩
    have h_eq2 : 4 + k^2 = k3^2 := by
      nlinarith [eq1]
    have h4 := h (-6)
    rcases h4 with ⟨k4, hk4⟩
    have h_eq3 : 9 + k^2 = k4^2 := by
      nlinarith [eq1]
    have h5 := h (-5)
    rcases h5 with ⟨k5, hk5⟩
    have h_eq4 : 16 + k^2 = k5^2 := by
      nlinarith [eq1]
    have h_1 : k = 0 := by
      have eq2 : k2^2 - k^2 = 1 := by
        nlinarith
      have eq3 : (k2 - k) * (k2 + k) = 1 := by
        nlinarith
      have h6 : k2 - k = 1 ∨ k2 - k = -1 := by 
        apply Int.eq_one_or_neg_one_of_mul_eq_one 
        exact eq3
      cases h6 with
      | inl h6 =>
        -- Assume k2 - k = 1
        have h7 : k2 + k = 1 := by
          nlinarith
        omega
      | inr h6 =>
        -- Assume k2 - k = -1
        have h7 : k2 + k = -1 := by
          nlinarith
        omega
    have hk0 : k^2 = 0 := by
      rw [show k = 0 by exact_mod_cast h_1]
      all_goals nlinarith
    have hc : c = 81 := by
      nlinarith [eq1, hk0]
    linarith