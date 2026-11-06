import Mathlib

/- A triangular array of 2016 coins has 1 coin in the first row, 
2 coins in the second row, 3 coins in the third row, and so on up 
to N coins in the Nth row. What is the sum of the digits of N?
(A) 6 (B) 7 (C) 8 (D) 9 (E) 10 -/
theorem number_theory_95815 (N : ℕ) 
(hN : 2016 = ∑ i ∈ Finset.range N, (i + 1)) :
(Nat.digits 10 N).sum = 9 := by {
  suffices : N = 63

  -- We first show that it suffices to show that N = 63. This is trivial.
  rw [this]
  norm_num

  -- Now we show that N = 63. We begin by showing that 4032 = N * (N + 1)
  rw [Finset.sum_add_distrib,Finset.sum_const] at hN
  simp at hN
  have hN₁ := congrArg (λ x : ℕ ↦ x*2) hN
  simp at hN₁
  rw [Nat.right_distrib,Finset.sum_range_id_mul_two,←Nat.left_distrib] at hN₁
  have h1 : N ≥ 1 := by {
    by_contra h1n
    simp at h1n
    rw [h1n] at hN₁
    trivial
  }
  have hN₂ : 4032 = N * (N + 1) := by {
    rw [←Nat.sub_add_comm h1] at hN₁
    rw [hN₁]
    norm_num
  }

  -- Now we need to deduce that N = 63. This is intuitively obvious,
  -- we use some simple linear arithmetic, showing both N ≤ 63 and 63 ≤ N.
  rw [Nat.eq_iff_le_and_ge]
  constructor

  -- Here we show that N ≤ 63
  by_contra h
  simp at h
  suffices : 4032 < 4032
  trivial
  calc 4032 = 63 * (63 + 1) := by norm_num
          _ < N * (63 + 1) := by {rw [Nat.mul_lt_mul_right]; exact h; trivial}
          _ < N * (N + 1) := by {rw [Nat.mul_lt_mul_left (by trivial),Nat.add_lt_add_iff_right] ; exact h}
          _ = 4032 := by rw [hN₂]

  -- And here 63 ≤ N.
  by_contra h
  simp at h
  suffices : 4032 < 4032
  trivial
  calc 4032 = N * (N + 1) := by rw [hN₂]
          _ < 63 * (N + 1) := by {rw [Nat.mul_lt_mul_right]; exact h; exact Nat.add_one_pos N}
          _ < 63 * (63 + 1) := by {rw [Nat.mul_lt_mul_left (by trivial),Nat.add_lt_add_iff_right]; exact h}
  
}