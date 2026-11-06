import Mathlib

theorem number_theory_128028 {p : Polynomial ℤ} (hc : ∃ c > 0, ∀ i ∈ Finset.Icc 1 c, ¬(c ∣ p.eval i)) :
    ∀ b : ℤ, p.eval b ≠ 0 := by
  rcases hc with ⟨c, hc_pos, hc⟩
  intro b
  by_contra h
  have h1 : ∀ (k : ℤ), (k - b) ∣ p.eval k := by
    intro k
    have h1 : (k - b : ℤ) ∣ p.eval k - p.eval b := by
      apply p.sub_dvd_eval_sub
    have h2 : p.eval k - p.eval b = p.eval k := by
      rw [show p.eval b = (0 : ℤ) by simpa using h]
      all_goals simp
    rw [h2] at h1
    exact h1
  have h2 : ∃ k : ℤ, k ∈ Finset.Icc 1 c ∧ (k - b) % c = 0 := by
    have h3 : (b % c : ℤ) ≥ 0 := by
      apply Int.emod_nonneg
      all_goals omega
    have h4 : (b % c : ℤ) ≥ 1 ∨ (b % c : ℤ) = 0 := by
      have h3' : (b % c : ℤ) ≥ 0 := h3
      omega
    rcases h4 with (h4 | h4)
    · -- case $b \pmod{c} \ge 1$.
      use b % c
      constructor
      · -- Show $k \in \{1, \ldots, c\}$.
        have h5 : b % c ≥ 1 := h4
        have h6 : b % c ≤ c - 1 := by
          have h7 : b % c < (c : ℤ) := by
            apply Int.emod_lt_of_pos
            linarith
          omega
        have h8 : b % c ≤ c := by omega
        exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
      · -- Show that $k - b$ is divisible by $c$.
        have h11 : (b % c - b : ℤ) % c = 0 := by
          have h12 : (b % c - b : ℤ) ≡ 0 [ZMOD c] := by
            have h17 : (b % c : ℤ) ≡ b [ZMOD c] := by
              exact Int.mod_modEq b c
            have h19 : (b % c - b : ℤ) ≡ 0 [ZMOD c] := by
              have h20 : (b % c : ℤ) ≡ b [ZMOD c] := h17
              have h19 : (b % c - b : ℤ) ≡ (b - b : ℤ) [ZMOD c] := by
                apply Int.ModEq.sub
                exact h20
                exact Int.ModEq.refl b
              simp at h19 ⊢
              exact h19
            exact h19
          exact h12
        omega
    · -- case $b \pmod{c} = 0$.
      use c
      constructor
      · -- Show $k \in \{1, \ldots, c\}$.
        exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
      · -- Show that $k - b$ is divisible by $c$.
        have h21 : (c - b : ℤ) % c = 0 := by
          have h22 : (c - b : ℤ) ≡ 0 [ZMOD c] := by
            have h20 : (b : ℤ) ≡ (0 : ℤ) [ZMOD c] := by
              have h24 : b % c = 0 := h4
              exact Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero (show b % c = 0 by omega))
            have h21 : (c : ℤ) ≡ (0 : ℤ) [ZMOD c] := by
              simp [Int.ModEq]
            have h22 : (c - b : ℤ) ≡ (0 - 0 : ℤ) [ZMOD c] := by
              apply Int.ModEq.sub
              exact h21
              exact h20
            simp at h22 ⊢
            exact h22
          exact h22
        omega
  rcases h2 with ⟨k, hk1, hk2⟩
  have h3 : c ∣ p.eval k := by
    have h31 : c ∣ (k - b : ℤ) := by
      have h32 : (k - b) % c = 0 := by omega
      exact Int.dvd_of_emod_eq_zero (show (k - b) % c = 0 by omega)
    have h33 : (k - b : ℤ) ∣ p.eval k := by
      apply h1
    exact dvd_trans h31 h33
  have h40 : ¬ (c ∣ p.eval k) := by
    apply hc k
    exact hk1
  contradiction