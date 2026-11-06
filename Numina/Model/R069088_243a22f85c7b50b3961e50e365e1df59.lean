import Mathlib

theorem number_theory_167665 : IsGreatest {m | 12^m ∣ Nat.factorial 100} 48 := by
  constructor
  · -- Show 48 is in the set.
    native_decide
  · -- Show if m is in the set, m ≤ 48
    intro m
    intro hm
    have h3 : 12^m ∣ Nat.factorial 100 := hm
    have h4 : m ≤ 48 := by
      by_contra h
      push_neg at h
      have h5 : m ≥ 49 := by omega
      have h6 : 12^49 ∣ 12^m := by
        apply pow_dvd_pow _ (by linarith)
      have h7 : 12^49 ∣ Nat.factorial 100 := by
        exact dvd_trans h6 h3
      have h8 : ¬ (3 ^ 49 ∣ Nat.factorial 100) := by
        native_decide
      have h9 : 3 ^ 49 ∣ Nat.factorial 100 := by
        have h10 : 3 ^ 49 ∣ 12 ^ 49 := by
          norm_num
          <;> omega
        exact dvd_trans h10 h7
      contradiction
      all_goals omega
    linarith