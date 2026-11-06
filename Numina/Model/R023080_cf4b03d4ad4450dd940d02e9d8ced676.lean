import Mathlib

theorem number_theory_9675 : IsGreatest {a | ∃ b : ℕ, 0 < a ∧ 0 < b ∧ Nat.factorial 2023 = 3^a * b} 1006 := by
  constructor
  · -- Show 1006 is in the set.
    use Nat.factorial 2023 / 3 ^ 1006
    native_decide
  · -- Show 1006 is the greatest.
    intro a ha
    rcases ha with ⟨b, ha_pos, hb_pos, heq⟩
    by_contra h
    push_neg at h
    have h1 : a ≥ 1007 := by omega
    -- Show that 3^1007 does not divide 2023!
    have h2 : ¬ (3 ^ 1007 ∣ Nat.factorial 2023) := by 
      native_decide
    -- Show that 3^a divides 2023!
    have h3 : 3 ^ a ∣ Nat.factorial 2023 := by 
      use b
      all_goals linarith
    -- Show that 3^1007 divides 3^a
    have h4 : 3 ^ 1007 ∣ Nat.factorial 2023 := by
      have h5 : 3 ^ 1007 ∣ 3 ^ a := by
        apply pow_dvd_pow _ (by omega)
      have h6 : 3 ^ a ∣ Nat.factorial 2023 := h3
      exact dvd_trans h5 h6
    exact h2 h4