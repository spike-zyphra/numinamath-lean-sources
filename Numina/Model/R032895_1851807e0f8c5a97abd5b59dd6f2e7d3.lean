import Mathlib

theorem algebra_133250 :
    IsGreatest {x | ∃ a b c : ℤ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∈ Finset.Icc 1 10 ∧ b ∈ Finset.Icc 1 10 ∧ c ∈ Finset.Icc 1 10 ∧ x = a * (b + c) - b * (a + c)} 81 := by
  constructor
  · -- Show that 81 is achievable with a = 10, b = 1, c = 9
    use 10, 1, 9
    all_goals norm_num [Finset.mem_Icc]
    <;> tauto
  · -- Show that no value greater than 81 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hx⟩
    rw [Finset.mem_Icc] at ha hb hc
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num at hx
    <;> omega