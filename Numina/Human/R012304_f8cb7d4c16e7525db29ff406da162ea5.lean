import Mathlib

/- 17. The sum of three integers, which are perfect squares, is divisible by nine. Prove that among them there are two numbers, the difference of which is divisible by nine. -/
theorem number_theory_204360 (a b c : ℤ) (ha : ∃ m, a = m^2) (hb : ∃ n, b = n^2)
    (hc : ∃ p, c = p^2) (h : 9 ∣ (a + b + c)) : 9 ∣ a - b ∨ 9 ∣ a - c ∨ 9 ∣ b - c := by
      --First, we show that the residues of squares modulo 9 are 0, 1 , 4, 7.
      have sq_residues_mod_9 : ∀ x : ℤ, x^2 % 9 = 0 ∨ x^2 % 9 = 1 ∨ x^2 % 9 = 4 ∨ x^2 % 9 = 7 := by
        intro x
        have residues_mod_9 : x % 9 = 0 ∨  x % 9 = 1 ∨  x % 9 = 2 ∨  x % 9 = 3 ∨  x % 9 = 4 ∨  x % 9 = 5 ∨  x % 9 = 6 ∨  x % 9 = 7 ∨  x % 9 = 8 := by omega
        rcases residues_mod_9 with h0|h1|h2|h3|h4|h5|h6|h7|h8
        --Case 0 : x % 9 = 0
        left
        have : 9 ∣ x := by exact Int.dvd_of_emod_eq_zero h0
        refine Int.emod_eq_zero_of_dvd ?_
        obtain ⟨k, hk⟩ := this
        rw [hk]
        have : (9 * k)^2 = 9 * (9 * k^2) := by ring
        rw [this]
        omega
        --Case 1 : x % 9 = 1.
        right; left
        have : (x - 1) % 9 = 0 := by omega
        have : 9 ∣ (x - 1) := by exact Int.dvd_sub_of_emod_eq h1
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 1 := by linarith
        rw [this]
        ring_nf
        omega
        --Case 2 : x % 9 = 2.
        right; right; left
        have : (x - 2) % 9 = 0 := by omega
        have : 9 ∣ (x - 2) := by exact Int.dvd_sub_of_emod_eq h2
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 2 := by linarith
        rw [this]
        ring_nf
        omega
        --Case 3 : x % 9 = 3.
        left
        have : (x - 3) % 9 = 0 := by omega
        have : 9 ∣ (x - 3) := by exact Int.dvd_sub_of_emod_eq h3
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 3 := by linarith
        rw [this]
        ring_nf
        omega
        --Case 4 : x % 9 = 4
        right; right; right
        have : (x - 4) % 9 = 0 := by omega
        have : 9 ∣ (x - 4) := by exact Int.dvd_sub_of_emod_eq h4
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 4 := by linarith
        rw [this]
        ring_nf
        omega
        --Case 5 : x % 9 = 5
        right; right; right
        have : (x - 5) % 9 = 0 := by omega
        have : 9 ∣ (x - 5) := by exact Int.dvd_sub_of_emod_eq h5
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 5 := by linarith
        rw [this]
        ring_nf
        omega
        --Case 6 : x % 9 = 6
        left
        have : (x - 6) % 9 = 0 := by omega
        have : 9 ∣ (x - 6) := by exact Int.dvd_sub_of_emod_eq h6
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 6 := by linarith
        rw [this]
        ring_nf
        omega
        --Case 7 : x % 9 = 7
        right; right; left
        have : (x - 7) % 9 = 0 := by omega
        have : 9 ∣ (x - 7) := by exact Int.dvd_sub_of_emod_eq h7
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 7 := by linarith
        rw [this]
        ring_nf
        omega
        --case 8 : x % 9 = 8
        right; left
        have : (x - 8) % 9 = 0 := by omega
        have : 9 ∣ (x - 8) := by exact Int.dvd_sub_of_emod_eq h8
        obtain ⟨k, hk⟩ := this
        have : x = 9 * k + 8 := by linarith
        rw [this]
        ring_nf
        omega
      --Use ha, hb, hc and obtain...
      obtain ⟨m, ham⟩ := ha
      obtain ⟨n, hbn⟩ := hb
      obtain ⟨p, hcp⟩ := hc
      --Substitute these into h.
      have div_squares : 9 ∣ m^2 + n^2 + p^2 := by
        rw [ham, hbn, hcp] at h
        exact h
      --Upon careful inspection, we see that at least two of m^2, n^2, and p^2 must be congruent to the same number modulo 9.
      --Compare this with sq_residues_mod_9
      --We prove this by contradiction.
      --First observe that m^2 + n^2 + p^2 equals 0 modulo 9.
      have pre_result0 : (m^2 + n^2 + p^2) % 9 = 0 := by exact Int.emod_eq_zero_of_dvd div_squares
      --Simplifying this congruence gives the following.
      have pre_result1 : (m^2 % 9 + n^2 % 9 + p^2 % 9) % 9 = 0 := by omega
      have lem : (m^2 % 9 = n^2 % 9) ∨ (m^2 % 9 = p^2 % 9) ∨ (n^2 % 9 = p^2 % 9) := by
        by_contra lem
        --Pushing the negation at lem gives the following equivalent form.
        have push_lem : m ^ 2 % 9 ≠  n ^ 2 % 9 ∧ m ^ 2 % 9 ≠ p ^ 2 % 9 ∧ n ^ 2 % 9 ≠ p ^ 2 % 9 := by tauto
        --From sq_residues_mod_9 we obtain the following.
        have sq_m : m^2 % 9 = 0 ∨ m^2 % 9 = 1 ∨ m^2 % 9 = 4 ∨ m^2 % 9 = 7 := by
          exact sq_residues_mod_9 m
        have sq_n : n^2 % 9 = 0 ∨ n^2 % 9 = 1 ∨ n^2 % 9 = 4 ∨ n^2 % 9 = 7 := by
          exact sq_residues_mod_9 n
        have sq_p : p^2 % 9 = 0 ∨ p^2 % 9 = 1 ∨ p^2 % 9 = 4 ∨ p^2 % 9 = 7 := by
          exact sq_residues_mod_9 p
        --We now do a case-analysis and derive a contradiction at each case.
        rcases sq_m with hm|hm|hm|hm <;>
        rcases sq_n with hn|hn|hn|hn <;>
        rcases sq_p with hp|hp|hp|hp <;>
        all_goals
        rw [hm, hn, hp] at push_lem
        rw [hm, hn, hp] at pre_result1
        omega
      --Going back to the orginals...
      rw [←ham, ←hbn, ←hcp] at lem
      rcases lem with h1|h2|h3
      --Now we attack each case separately.
      left
      exact Int.ModEq.dvd (id (Eq.symm h1))
      right; left
      exact Int.ModEq.dvd (id (Eq.symm h2))
      right; right
      exact Int.ModEq.dvd (id (Eq.symm h3))