import Mathlib

theorem number_theory_4855 :
    Set.ncard {n : ℕ+ | n.val + 1 ∣ n.val ^ 2 + 2023} = 15 := by
  have h1 : {n : ℕ+ | n.val + 1 ∣ n.val ^ 2 + 2023} = Finset.filter (fun y : ℕ+ => y.val + 1 ∣ y.val ^ 2 + 2023) (Finset.Icc (1 : ℕ+) 2024) := by
    ext y
    simp
    intro h
    have h2 : y.val + 1 ∣ y.val ^ 2 + 2023 := h
    -- Now we show that $y + 1$ divides $2024$.
    have h3 : y.val + 1 ∣ 2024 := by
      have h4 : y.val + 1 ∣ y.val ^ 2 + 2023 := h2
      have h5 : y.val + 1 ∣ (y.val + 1) * (y.val - 1) := by
        apply dvd_mul_right
      have h6 : y.val + 1 ∣ (y.val ^ 2 + 2023 - ((y.val + 1) * (y.val - 1))) := by
        apply Nat.dvd_sub'
        · exact h4
        · exact h5
      have h7 : y.val ^ 2 + 2023 - ((y.val + 1) * (y.val - 1)) = 2024 := by
        by_cases h9 : y.val > 1
        · 
          have h20 : y.val - 1 > 0 := by
            have h10 : y.val > 1 := h9
            omega
          cases y with
          | mk n hn =>
            simp at *
            <;> cases n with
            | zero => linarith
            | succ n => 
              cases n with
              | zero => linarith
              | succ n => 
                simp [Nat.mul_sub, Nat.add_sub_cancel'] at *
                <;> ring_nf <;> omega
        · 
          have h11 : y.val = 1 := by
            have h12 : y.val > 0 := by
              exact_mod_cast y.prop
            have h12 : y.val ≤ 1 := by
              omega
            interval_cases y.val <;> try { tauto }
          rw [h11] at *
          all_goals
            norm_num
      rw [h7] at h6
      exact_mod_cast h6
    -- We have that $y + 1$ divides $2024$, so $y + 1 \leq 2024$.
    -- Therefore $y \leq 2024$.
    have h14 : y.val + 1 ≤ 2024 := by
      exact Nat.le_of_dvd (by norm_num) h3
    have h15 : y.val ≤ 2024 := by
      omega
    exact_mod_cast h15
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide