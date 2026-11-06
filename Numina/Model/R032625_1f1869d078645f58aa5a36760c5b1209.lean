import Mathlib

theorem algebra_15626 (x : ℕ) (h : 3 ^ x + 4 ^ x + 5 ^ x = 6 ^ x) :
    x = 3 := by
        have h1 : x = 3 := by 
            have h2 : x ≤ 3 := by
                by_contra h3
                push_neg at h3
                have h4 : x ≥ 4 := by omega
                have h8 : 3 ^ x + 4 ^ x + 5 ^ x < 6 ^ x := by 
                    have h9 : x ≥ 4 := h4
                    have h10 : ∀ (n : ℕ), 3 ^ (n + 4) + 4 ^ (n + 4) + 5 ^ (n + 4) < 6 ^ (n + 4) := by
                        intro n
                        induction n with
                        | zero =>
                            norm_num
                        | succ n ih =>
                            ring_nf at ih ⊢
                            omega
                    have h11 := h10 (x - 4)
                    have h12 : (x - 4) + 4 = x := by 
                        omega 
                    rw [h12] at h11 
                    linarith
                linarith
            interval_cases x <;> norm_num at h ⊢
            all_goals linarith
        linarith