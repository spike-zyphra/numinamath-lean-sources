import Mathlib

theorem number_theory_7993 :
    {(m, n) : ℕ × ℕ | m.Prime ∧ n.Prime ∧ m < n ∧ n < 3 * m ∧ (m + 3 * n).Prime}.ncard = 2 := by
  have h : {(m, n) : ℕ × ℕ | m.Prime ∧ n.Prime ∧ m < n ∧ n < 3 * m ∧ (m + 3 * n).Prime} = {(2, 3), (2, 5)} := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- First implication: if (m, n) is in the set, then it equals either (2, 3) or (2, 5)
      rintro ⟨h1, h2, h3, h4, h5⟩
      by_cases h6 : m > 2
      · -- Assume m > 2
        have h7 : m % 2 = 1 := by
          by_contra h
          push_neg at h
          have : m > 2 := by linarith
          have : ¬m.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ m by omega)
            all_goals linarith
          contradiction
        have h8 : n % 2 = 1 := by 
          by_contra h
          push_neg at h
          have : n % 2 = 0 := by omega
          have : n > 2 := by nlinarith [show m > 0 by linarith, h3, h4]
          have : ¬n.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega)
            all_goals linarith
          contradiction
        have h9 : (m + 3 * n) % 2 = 0 := by
          omega
        have h10 : (m + 3 * n) > 2 := by
          nlinarith
        have h11 : ¬ (m + 3 * n).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (m + 3 * n) by omega)
          all_goals omega
        contradiction
      · -- Assume m ≤ 2
        have : m = 2 := by
          interval_cases m <;> norm_num at h1 ⊢
        subst this
        have h6 : n < 3 * 2 := h4
        interval_cases n <;> norm_num at h2 h3 h4 h5 ⊢ <;> tauto
    · -- Second implication: if (m, n) equals either (2, 3) or (2, 5), then it is in the set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (2, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · native_decide
      · -- Check (2, 5)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · native_decide
  rw [h]
  rw [Set.ncard_pair]
  all_goals norm_num