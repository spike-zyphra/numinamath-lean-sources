import Mathlib


theorem number_theory_165729 :
    Nat.card {n : ℕ | (n ^ 2 + 1983) % (n + 1983) = 0} = 29 := by
  have h1 : {n : ℕ | (n ^ 2 + 1983) % (n + 1983) = 0} = Finset.filter (fun n => (n ^ 2 + 1983) % (n + 1983) = 0) (Finset.Iic (1983 * 1984)) := by
    ext n
    simp
    intro h
    have h2 : (n + 1983) ∣ (n ^ 2 + 1983) := by
      have h4 : (n ^ 2 + 1983) % (n + 1983) = 0 := h
      exact Nat.dvd_of_mod_eq_zero h4
    have h30 : (n + 1983) ∣ (1983 ^ 2 + 1983) := by
      have h20 : (n + 1983 : ℤ) ∣ (n ^ 2 + 1983 : ℤ) := by
        exact_mod_cast h2
      have h40 : (n + 1983 : ℤ) ∣ ((n ^ 2 + 1983 : ℤ) - (n + 1983 : ℤ) * ((n : ℤ) - 1983)) := by
        apply Dvd.dvd.sub h20
        apply dvd_mul_right
      have h22 : ((n ^ 2 + 1983 : ℤ) - (n + 1983 : ℤ) * ((n : ℤ) - 1983)) = (1983 ^ 2 + 1983 : ℤ) := by
        cases n with
        | zero =>
          norm_num
        | succ n =>
          cases n with
          | zero =>
            norm_num
          | succ n =>
            cases n with
            | zero =>
              norm_num
            | succ n =>
              cases n with
              | zero =>
                norm_num
              | succ n =>
                zify
                ring_nf
                <;> omega
      rw [h22] at h40
      exact_mod_cast h40
    have h31 : (n + 1983) ≤ 1983 * 1984 := by
      exact Nat.le_of_dvd (by norm_num) h30
    have h32 : n ≤ 1983 * 1984 := by
      omega
    linarith
  rw [h1]
  rw [Nat.card_eq_fintype_card]
  simp
  native_decide