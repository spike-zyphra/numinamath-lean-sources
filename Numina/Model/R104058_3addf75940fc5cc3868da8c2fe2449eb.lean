import Mathlib

theorem number_theory_243757 : IsGreatest {k | 0 < k ∧ 7^k ∣ Nat.factorial 50} 8 := by 
  constructor 
  · -- Check 8 is in the set
    constructor
    · norm_num
    · native_decide
  · -- Show that any element k in the set satisfies k ≤ 8
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    by_contra h 
    push_neg at h
    have h9 : k ≥ 9 := by omega
    have h10 : 7 ^ 9 ∣ 7 ^ k := by 
      apply pow_dvd_pow _ (by omega)
    have h11 : 7 ^ 9 ∣ Nat.factorial 50 := by 
      apply dvd_trans h10 hk_div
    have h12 : ¬ (7 ^ 9 ∣ Nat.factorial 50) := by
      native_decide
    exact h12 h11