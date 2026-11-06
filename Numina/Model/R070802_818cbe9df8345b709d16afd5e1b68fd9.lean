import Mathlib

theorem algebra_138448 {G : Type*} [Group G] [Fintype G] (g : G) :
    orderOf g ∣ (Fintype.card G : ℕ) := by
  apply orderOf_dvd_card