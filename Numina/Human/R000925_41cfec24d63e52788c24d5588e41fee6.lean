import Mathlib

/-What is the units digit of $3^1 + 3^3 + 3^5 + 3^7 + \ldots + 3^{2009}$?-/
theorem number_theory_19141 : (∑ i ∈ Finset.range 1005, 3 ^ (2 * i + 1)) % 10 = 3 := by
  -- show that 3 ^ (4 * n + 1) % 10 = 3
  have h1 : ∀ n : ℕ, 3 ^ (4 * n + 1) % 10 = 3 := by
    intro n
    induction n with -- prove by induction
    | zero => norm_num -- when n = 0
    | succ n hn => -- when n satisfied, show the case of n + 1
      calc
        3 ^ (4 * (n + 1) + 1) % 10 = (3 ^ (4 * n + 1)) * (3 ^ 4) % 10 := by ring_nf
        _ = 3 * 3 ^ 4 % 10 := by rw [<-Nat.mod_mul_mod]; rw [hn]
        _ = 3 := by norm_num
  -- show that 3 ^ (4 * n + 3) % 10 = 7
  have h3 : ∀ n : ℕ, 3 ^ (4 * n + 3) % 10 = 7 := by
    intro n
    induction n with -- prove by induction
    | zero => norm_num -- when n = 0
    | succ n hn => -- when n satisfied, show the case of n + 1
      calc
        3 ^ (4 * (n + 1) + 3) % 10 = (3 ^ (4 * n + 3)) * (3 ^ 4) % 10 := by ring_nf
        _ = 7 * 3 ^ 4 % 10 := by rw [<-Nat.mod_mul_mod]; rw [hn]
        _ = 7 := by norm_num
  -- show the stronger conclusion
  rw [Finset.sum_nat_mod]
  have h (n : ℕ) : (∑ i ∈ Finset.range n, 3 ^ (2 * i + 1) % 10 ) % 10 = (if 2 ∣ n then 0 else 3) := by
    -- prove by induction of n
    induction n with
    | zero => simp -- when n = 0, obviously
    | succ n hn => -- when n satisfied
      -- divide into two cases 2 ∣ n or ¬2 | n
      have casen : 2 ∣ n ∨ ¬2 ∣ n := by tauto
      cases casen with
      -- when ¬2 ∣ n
      | inr hn2 =>
        -- try to find some m, s.t n = 2 * m + 1
        simp [hn2, show 2 ∣ n + 1 by rw [Nat.two_dvd_ne_zero] at hn2; apply Nat.dvd_of_mod_eq_zero; rw [Nat.add_mod, hn2]] at hn ⊢
        rw [Finset.sum_range_add]
        simp
        rw [Nat.add_mod, hn]
        simp at hn2
        have hn3 := hn2
        apply Nat.two_mul_odd_div_two at hn2
        -- show that 2 * (n / 2) + 1 = n (for the type of ℕ, the proof of 1 ≤ n waste some times)
        replace hn2 : 2 * (n / 2) + 1 = n := by
          symm at hn2 ⊢
          apply Nat.eq_add_of_sub_eq
          cases n with
          | zero => norm_num at hn3 ⊢
          | succ n => linarith
          exact hn2
        have h := h3 (n / 2)
        -- calculate (3 + 3 ^ (2 * n + 1) % 10) % 10 = 0
        calc
          (3 + 3 ^ (2 * n + 1) % 10) % 10 = (3 + 3 ^ (2 * (2 * (n / 2) + 1) + 1) % 10) % 10 := by rw [hn2]
          _ = (3 + 3 ^ (4 * (n / 2) + 3) % 10) % 10 := by ring_nf
          _ = (3 + 7) % 10 := by rw [h]
          _ = 0 := by norm_num
      -- when 2 ∣ n
      | inl hn2 =>
        -- try to find some m, s.t n = 2 * m
        simp [hn2, show ¬2 ∣ n + 1 by rw [Nat.two_dvd_ne_zero, Nat.add_mod]; rw [Nat.dvd_iff_mod_eq_zero] at hn2; rw [hn2]] at hn ⊢
        rw [Finset.sum_range_add]
        simp
        rw [Nat.add_mod, hn]
        -- show that n = 2 * (n / 2)
        apply Nat.mul_div_cancel' at hn2
        norm_num
        -- calculate that 3 ^ (2 * n + 1) % 10 = 3
        have h := h1 (n / 2)
        calc
          3 ^ (2 * n + 1) % 10 = 3 ^ (2 * (2 * (n / 2)) + 1) % 10 := by rw [hn2]
          _ = 3 ^ (4 * (n / 2) + 1) % 10 := by ring_nf
          _ = 3 := by rw [h]
  -- sepecialize the n to 1005, exact the conclusion
  replace h := h 1005
  simp [show ¬2 ∣ 1005 by norm_num] at h
  exact h