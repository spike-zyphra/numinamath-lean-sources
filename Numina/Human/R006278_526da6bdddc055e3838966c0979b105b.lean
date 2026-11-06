import Mathlib

def S n := (Nat.digits 10 n).sum

/- Let $k$ be a positive integer. Suppose there exist positive natural numbers $n$ and $m$ such that $n = k \cdot m$ and the sum of the base-10 digits of $n$ is equal to $k$ times one less than the sum of the base-10 digits of $m$. Show that $k$ must be a multiple of 9. -/
theorem number_theory_635471
  (k : ℕ)
  (hk : 0 < k)
  (n m : ℕ)
  (hn : 0 < n)
  (hm : 0 < m)
  (hnm : n = k * m)
  (hsum : S n = k * (S m - 1))
  : 9 ∣ k :=
by
  apply Nat.dvd_of_mod_eq_zero
  change k ≡ 0 [MOD 9]
  have : S n ≡ k * m [MOD 9] := by
    symm
    rw [hnm]
    simp [S]
    exact Nat.modEq_nine_digits_sum (k * m)
  rw [hsum] at this
  have : k * m ≡ k * (m - 1) [MOD 9] := by
    have : S m - 1 ≡ m - 1 [MOD 9] := by
      symm
      simp [S]
      apply Nat.ModEq.add_right_cancel' 1
      rw [Nat.sub_add_cancel, Nat.sub_add_cancel]
      exact Nat.modEq_nine_digits_sum m
      apply Nat.one_le_iff_ne_zero.mpr
      . intro h
        -- Hard part.
        -- Show that digits sum is not zero.
        have : ∀ x ∈ Nat.digits 10 m, x = 0 := by
          by_contra h'
          push_neg at h'
          rcases h' with ⟨x, h'⟩
          have : (Nat.digits 10 m).sum ≥ x := by
            apply List.le_sum_of_mem
            tauto
          omega
        have : Nat.ofDigits 10 (Nat.digits 10 m) = 0 := by
          have : Nat.digits 10 m = List.replicate (Nat.digits 10 m).length 0 := by
            exact List.eq_replicate_of_mem this
          rw [this]
          induction (Nat.digits 10 m).length with
          | zero => simp
          | succ l ih =>
            simp [List.replicate, Nat.ofDigits]
            assumption
        have : m = 0 := by
          trans Nat.ofDigits 10 (Nat.digits 10 m)
          . exact Eq.symm (Nat.ofDigits_digits 10 m)
          . assumption
        omega
      omega
    have : k * (S m - 1) ≡ k * (m - 1) [MOD 9] := by
      exact Nat.ModEq.mul rfl this
    symm
    trans
    . symm at this
      exact this
    . assumption
  -- rest part is trivial.
  rw [Nat.mul_sub] at this
  simp [Nat.ModEq] at this
  zify at this
  change _ ≡ _ [ZMOD 9] at this
  have : 0 ≡ - k [ZMOD 9] := by
    rw [Nat.cast_sub] at this
    exact Int.ModEq.symm (Int.ModEq.add_left_cancel' (↑(k * m)) (id (Int.ModEq.symm this)))
    exact Nat.le_mul_of_pos_right k hm
  simp [Nat.ModEq]
  simp [Int.ModEq] at this
  omega
