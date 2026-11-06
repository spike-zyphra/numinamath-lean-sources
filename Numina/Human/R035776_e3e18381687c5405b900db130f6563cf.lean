import Mathlib

/- 12.79 Prove that there do not exist integers \(x, y, z\) such that the equation \(x^{k} + y^{k} = z^{k}\) holds under the conditions \(z > 0, 0 < x < k, 0 < y < k\), where \(k\) is a natural number.
(22nd Moscow Mathematical Olympiad, 1959) -/

-- ** Autoformalization had an extra z > 0 after 0 < z. **
theorem number_theory_170899 (k : ℕ) :
    ¬∃ x y z : ℤ, 0 < z ∧ 0 < x ∧ x < k ∧ 0 < y ∧ y < k ∧ x ^ k + y ^ k = z ^ k := by

  -- We prove by contradiction.
  -- Assume that there exist integers \(x, y, z\) such that the equation
  -- \(x^{k} + y^{k} = z^{k}\) holds under the conditions \(z > 0, 0 < x < k, 0 < y < k\),
  -- where \(k\) is a natural number.
  by_contra h

  -- We can assume that \(x, y, z\) are in fact natural numbers because of
  -- \(z > 0, 0 < x, 0 < y\)
  obtain ⟨ a, b, c, ⟨ hc, ha0, hak, hb0, hbk, habc ⟩ ⟩ := h
  have : ∃ x y z : ℕ, 0 < z ∧ 0 < x ∧ x < k ∧ 0 < y ∧ y < k ∧ x ^ k + y ^ k = z ^ k := by
    have : ∃ x : ℕ, x = a := by exact CanLift.prf a (Int.le_of_lt ha0)
    obtain ⟨ x, hx ⟩ := this
    have : ∃ y : ℕ, y = b := by exact CanLift.prf b (Int.le_of_lt hb0)
    obtain ⟨ y, hy ⟩ := this
    have : ∃ z : ℕ, z = c := by exact CanLift.prf c (Int.le_of_lt hc)
    obtain ⟨ z, hz ⟩ := this
    use x, y, z
    rw [← hx, ←hy, ←hz] at habc
    norm_cast at habc
    aesop
  clear a b c hc ha0 hak hb0 hbk habc

  obtain ⟨ x, y, z, ⟨ hz, hx0, hxk, hy0, hyk, heq ⟩ ⟩ := this

  -- Assume without loss of generality that \(x \leq y\).
  wlog g : x ≤ y
  . simp at g
    obtain s := this k y x z hz hy0 hyk hx0 hxk
    apply s
    rw [← heq]
    ring_nf
    exact Nat.le_of_lt g
  . -- Since \(x \leq y\), we have ()x ^ k \leq y ^ k\)
    have claim1 : x ^ k ≤ y ^ k := by
      refine pow_le_pow_left₀ ?_ g k
      exact Nat.le_of_lt hx0

    -- It follows that \(z ^ k = x ^ k + y ^ k \leq y ^ k + y ^ k\).
    have claim2 : z ^ k ≤ y ^ k + y ^ k:= by omega

    -- Now \(z ^ k \leq y ^ k + y ^ k < y ^ k + k * y ^ (k - 1) \) since \(y < k\)
    -- An easy induction gives \(y ^ k + k * y ^ (k - 1) \leq (y + 1)^k\).
    -- Hence, \(z ^ k < (y + 1) ^ k\).
    have claim3 : z ^ k < (y + 1) ^ k := by
      calc
        _ ≤ y ^ k + y ^ k:= claim2
        _ ≤ y ^ k + y * y ^ (k - 1) := by
            suffices y ^ k = y * y ^ (k - 1) by
              exact Nat.le_of_eq (congrArg (HAdd.hAdd (y ^ k)) this)
            refine Eq.symm (mul_pow_sub_one ?_ y)
            exact Nat.not_eq_zero_of_lt hxk
        _ < y ^ k + k * y ^ (k - 1) := by
            suffices y * y ^ (k - 1) < k * y ^ (k - 1) by
              exact Nat.add_lt_add_left this (y ^ k)
            suffices y < k by
              refine Nat.mul_lt_mul_of_pos_right hyk ?_; exact Nat.pos_pow_of_pos (k - 1) hy0
            exact hyk
        _ ≤ _ := by
          have (m : ℕ) : y ^ (m + 1) + (m + 1) * y ^ m ≤ (y + 1)^ (m + 1) := by
            induction m with
            | zero => simp
            | succ m ih =>
              calc
                _ = (y ^ (m + 1) + (m + 1 + 1) * y ^ m) * y := by rw [pow_add, pow_add, pow_one]
                                                                  ring
                _ = (y ^ (m + 1) + (m + 1) * y ^ m) * y + y ^ (m + 1) := by ring
                _ ≤ (y + 1) ^ (m + 1) * y + y ^ (m + 1) := by
                      apply Nat.add_le_add_right
                      exact Nat.mul_le_mul_right y ih
                _ ≤ _ := by rw [pow_add _ (m + 1), pow_one]
                            rw [mul_add, mul_one]
                            apply Nat.add_le_add_left
                            exact Nat.le_of_add_right_le ih
          have : ∃ r, k = r + 1 := by refine Nat.exists_eq_add_one.mpr ?_; omega
          obtain ⟨ r, hr ⟩ := this
          rw [hr]
          simp
          exact (this r)

    -- It follows that \(z < (y + 1)\).
    have claim4 : z < (y + 1) := by
      rw [Nat.pow_lt_pow_iff_left] at claim3
      . exact claim3
      . exact Nat.not_eq_zero_of_lt hxk

    -- But \(z ^ k = x ^ k + y ^ k\) implies that \(z ^ k > y ^ k\).
    -- Hence, \(y < z\).
    have claim5 : y < z := by
      suffices y ^ k < z ^ k by exact lt_of_pow_lt_pow_left' k this
      rw [← heq]
      refine Nat.lt_add_of_pos_left ?_
      exact Nat.pos_pow_of_pos k hx0

    -- But then \(y < z < y + 1\). Since ()z\) is a natural number,
    -- this is impossible.
    linarith