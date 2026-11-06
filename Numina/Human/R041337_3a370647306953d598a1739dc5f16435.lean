import Mathlib

/-Prove that there does not exist a three-digit number abc such that abc+bca+cab
is a perfect square -/
theorem number_theory_118918 :
    ¬∃ a b c : ℕ, a ∈ Finset.Icc 1 9 ∧ b ∈ Finset.Icc 0 9 ∧ c ∈ Finset.Icc 0 9 ∧
      IsSquare ((100 * a + 10 * b + c) + (100 * b + 10 * c + a) + (100 * c + 10 * a + b)) := by
        rintro ⟨a, b, c, ha, hb, hc, h⟩
        have h1 : a ≥ 1 := by
            simp at ha
            linarith
        have h2 : a ≤ 9 := by
            simp at ha
            linarith
        have h3 : b ≤ 9 := by
            simp at hb
            linarith
        have h4 : b ≥ 0 := by
            simp at hb
            linarith
        have h5 : c ≤ 9 := by
            simp at hc
            linarith
        have h6 : c ≥ 0 := by
            simp at hc
            linarith
        have eq : (100 * a + 10 * b + c) + (100 * b + 10 * c + a) + (100 * c + 10 * a + b) = 111 * (a + b + c) := by
            ring
        rw [eq] at h
        have h7 : a + b + c ≤ 27 := by
            linarith
        have h8 : ¬IsSquare (111 * (a + b + c)) := by 
            intro h9
            have h10 : a + b + c ≤ 27 := h7
            have h11 : a + b + c ≥ 1 := by 
                omega
            rw [isSquare_iff_exists_sq] at h9
            rcases h9 with ⟨m, hm⟩
            have h12 : m ≤ 54 := by
                nlinarith [sq_nonneg m, h7, hm]
            -- now we have obtained an upper bound of m, so we can just enumerate
            interval_cases m <;> omega
        contradiction