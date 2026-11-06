import Mathlib

/-
Let $n$ be a positive integer and $b$ be an integer greater than 1. Determine the number of digits in the base $b$ representation of $n!$. Show the answer is $\lfloor \log_b(n!) \rfloor + 1$.
-/

theorem number_theory_636777 (n b : ℕ) (npos: 0 < n) (bg1: 1 < b):
  (b.digits (Nat.factorial n)).length = ⌊(Real.logb b (Nat.factorial n))⌋ + 1 := by

  --We use the result that the length of digits is (Nat.log b n.factorial).
  rw [Nat.digits_len]
  simp
  have b1: 0 ≤ Real.logb ↑b ↑n.factorial := by 
    refine Real.logb_nonneg ?_ ?_
    norm_cast
    norm_cast
    refine Nat.one_le_iff_ne_zero.mpr ?_
    exact Nat.factorial_ne_zero n
  have b2: 0 ≤ ⌊Real.logb ↑b ↑n.factorial⌋ := by 
    exact Int.floor_nonneg.mpr b1
  have e : ⌊Real.logb ↑b ↑n.factorial⌋.toNat = ⌊Real.logb ↑b ↑n.factorial⌋ := by 
    exact Int.toNat_of_nonneg b2
  
  --Now we just need to verrify that (Nat.log b n.factorial) is equal to the one claimed.
  --This follows from the definition of Nat.log and ⌊ ⌋.
  have cla : (Nat.log b n.factorial) = ⌊Real.logb ↑b ↑n.factorial⌋.toNat := by
    refine (Nat.log_eq_iff ?_).mpr ?_

    right
    simp [bg1]
    exact Nat.factorial_ne_zero n

    constructor
    
    have t1 : ⌊Real.logb ↑b ↑n.factorial⌋.toNat ≤ Real.logb ↑b ↑n.factorial := by 
      rify at e
      rw [e]
      exact Int.floor_le (Real.logb ↑b ↑n.factorial)
    have t1' : (b:ℝ) ^ (⌊Real.logb ↑b ↑n.factorial⌋.toNat:ℝ) ≤ b ^ (Real.logb ↑b ↑n.factorial) := by
      rw [Real.rpow_le_rpow_left_iff]
      exact t1
      norm_cast
    have t2 : b ^ ⌊Real.logb ↑b ↑n.factorial⌋.toNat ≤ (b:ℝ) ^ Real.logb ↑b ↑n.factorial := by 
      norm_cast at t1' ⊢
    have t3 : (b:ℝ) ^ Real.logb ↑b ↑n.factorial = n.factorial := by
      refine Real.rpow_logb ?_ ?_ ?_
      norm_cast; linarith
      norm_cast; linarith
      norm_cast; exact Nat.factorial_pos n

    rw [t3] at t2
    norm_cast at t2
    

    have t1 : (b:ℝ) ^ Real.logb ↑b ↑n.factorial = n.factorial := by
      refine Real.rpow_logb ?_ ?_ ?_
      norm_cast; linarith
      norm_cast; linarith
      norm_cast; exact Nat.factorial_pos n
    rify
    nth_rw 1 [← t1]
    have t2 : (b:ℝ) ^ Real.logb ↑b ↑n.factorial < ↑b ^ (⌊Real.logb ↑b ↑n.factorial⌋.toNat + (1:ℝ)) := by
      rw [Real.rpow_lt_rpow_left_iff]
      have : ⌊Real.logb ↑b ↑n.factorial⌋.toNat = ⌊Real.logb ↑b ↑n.factorial⌋ := by
        exact e
      rify at this
      rw [this]
      exact Int.lt_floor_add_one (Real.logb ↑b ↑n.factorial)
      norm_cast
    norm_cast at t2 ⊢

    

  zify at cla
  rw [e] at cla
  exact cla
  exact bg1
  exact Nat.factorial_ne_zero n

