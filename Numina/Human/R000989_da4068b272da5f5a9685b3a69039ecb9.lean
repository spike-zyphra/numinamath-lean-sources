import Mathlib

/-Let $m$ be a positive integer, and suppose that $9$ is its own inverse $\pmod m$, but $3$ is $\textbf{not}$ its own inverse $\pmod m$.

How many possible values for $m$ are there?-/
theorem number_theory_19601 :
    Set.encard {m : ℕ | 0 < m ∧ 9 * 9 ≡ 1 [ZMOD m] ∧ ¬(3 * 3 ≡ 1 [ZMOD m])} = 6 := by
    -- Only need to prove the required set equal  {5, 10, 16, 20, 40, 80}
    suffices {m : ℕ | 0 < m ∧ 9 * 9 ≡ 1 [ZMOD m] ∧ ¬(3 * 3 ≡ 1 [ZMOD m])} = {5, 10, 16, 20, 40, 80} by
      rw [this]
      have : ({5, 10, 16, 20, 40, 80} : Set ℕ).encard = ({5, 10, 16, 20, 40, 80} : Finset ℕ).card := by
        apply  Set.encard_eq_coe_toFinset_card
      simp [this]
    ext x
    simp
    constructor
    · -- the required set subsets  {5, 10, 16, 20, 40, 80}
      intro ⟨xpos, h1, h2⟩
      have h3 (a : ℕ) (ha : 1 ≤  a) : (a ≡ 1 [ZMOD x]) ↔ x ∣ a - 1 := by
        rw [Int.modEq_iff_dvd, ←Int.dvd_neg]
        simp
        norm_cast
      have := (h3 81 (by omega)).1 h1
      contrapose! h2
      change (9 : ℕ) ≡ 1 [ZMOD x]
      rw [h3 9 (by omega)]
      norm_num at this ⊢
      have h4 := Nat.le_of_dvd (by omega) this
      interval_cases x <;> norm_num at this h2 ⊢
    · --  {5, 10, 16, 20, 40, 80} subsets the required set.
      intro h
      rcases h with h | h | h | h | h | h <;> simp [h] <;> decide


