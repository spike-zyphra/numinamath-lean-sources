import Mathlib

/- Five aluminum cans can be recycled to make a new can. How many new cans can eventually be made from 125 aluminum cans? (Remember that the first new cans that are made can then be recycled into even newer cans!) -/
theorem algebra_21303 {n : ℕ} (hn : n = 125) :
    ∑' (i : ℕ), n / 5 ^ (i + 1)  = 31 := by
        -- 先证明第3项以后的项均为零
        have h1 : ∀ i ∉ ({0, 1, 2} : Finset ℕ), 125 / 5 ^ (i + 1) = 0:= by
            intro i hi
            simp at hi
            rcases hi with ⟨hi0, hi1, hi2⟩
            replace hi : i + 1 ≥ 4  := by omega
            have h1 : 5 ^ (i + 1) ≥ 5 ^ 4:= by
                rify
                refine pow_le_pow_right (by linarith) hi
            have h2 : 125 / 5 ^ (i + 1) ≤ 125 / 5 ^ 4:= by refine Nat.div_le_div_left h1 (by omega)
            rw [show 125 / 5 ^ 4 = 0 by omega] at h2
            have h3 : 125 / 5 ^ (i + 1) ≥ 0:= by exact Nat.zero_le (125 / 5 ^ (i + 1))
            omega
        -- 化为有限项求和
        have h2 : ∑' (i : ℕ), 125 / 5 ^ (i + 1) = ∑ (i ∈ ({0, 1, 2} : Set ℕ)), 125 / 5 ^ (i + 1):= tsum_eq_sum h1
        rw [hn, h2]
        -- 即证得结论
        simp
