import Mathlib

theorem number_theory_133112 :
    IsLeast {n | n ≥ 100 ∧ 3 ∣ n ∧ 13 ∣ n} 117 := by
  constructor
  · -- Show that 117 is in the set
    show 117 ≥ 100 ∧ 3 ∣ 117 ∧ 13 ∣ 117
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that for all n in the set, n ≥ 117
    intro n hn
    rcases hn with ⟨h100, h3, h13⟩
    have h39 : 39 ∣ n := by
      have h1 : 3 ∣ n := h3
      have h2 : 13 ∣ n := h13
      have h3 : Nat.Coprime 3 13 := by norm_num
      have h4 : Nat.lcm 3 13 ∣ n := Nat.lcm_dvd h1 h2
      have h5 : Nat.lcm 3 13 = 39 := by
        norm_num [Nat.lcm]
      rw [h5] at h4
      exact h4
    omega