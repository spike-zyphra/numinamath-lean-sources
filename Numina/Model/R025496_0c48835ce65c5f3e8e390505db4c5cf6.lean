import Mathlib

theorem number_theory_242510 : IsGreatest {k | 0 < k ∧ k^2 ∣ Nat.factorial 10} 720 := by
  constructor
  · -- Show 720 is in the set
    constructor
    · norm_num
    · -- Show 720^2 divides 10!
      native_decide
  · -- Show 720 is the greatest in the set
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    by_contra h
    push_neg at h
    have h1 : k > 720 := h
    have h2 : k ^ 2 ∣ Nat.factorial 10 := hk_div
    have h3 : k ≤ 1904 := by
      by_contra h6
      push_neg at h6
      have h7 : k ≥ 1905 := by omega
      have h8 : k ^ 2 > Nat.factorial 10 := by
        have h9 : k ≥ 1905 := h7
        have h10 : k ^ 2 ≥ 1905 ^ 2 := by nlinarith
        have h11 : 1905 ^ 2 > Nat.factorial 10 := by
          norm_num [Nat.factorial]
        nlinarith
      have h9 : k ^ 2 ≤ Nat.factorial 10 := by
        exact Nat.le_of_dvd (by positivity) h2
      linarith
    interval_cases k <;> norm_num [Nat.factorial] at h2 ⊢ <;> try { contradiction }