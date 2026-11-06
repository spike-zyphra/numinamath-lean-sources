import Mathlib

theorem number_theory_253318 :
    (Nat.factorial 7 / Nat.factorial 5 = 42) ∧
    (∀ n, n > 0 ∧ Nat.factorial 98 * 9900 = Nat.factorial n → n = 100) ∧
    (∀ m, m > 0 ∧ Nat.factorial (m + 2) / Nat.factorial m = 40200 → m = 199) ∧
    (∀ q, 0 < q → ∀ r, Nat.factorial (q + 2) - Nat.factorial (q + 1) = Nat.factorial q * r → IsSquare r) := by
  constructor
  · -- Proof of (a): Nat.factorial 7 / Nat.factorial 5 = 42
    native_decide
  constructor
  · -- Proof of (b): ∀ n, n > 0 ∧ Nat.factorial 98 * 9900 = Nat.factorial n → n = 100
    intro n h
    rcases h with ⟨hn_pos, heq⟩
    have h1 : n ≥ 99 := by
      by_contra h
      push_neg at h
      have h2 : n ≤ 98 := by linarith
      have eq1 : Nat.factorial n ≤ Nat.factorial 98 := by
        apply Nat.factorial_le
        linarith
      have eq2 : Nat.factorial 98 * 9900 ≤ Nat.factorial 98 := by
        have eq11 : Nat.factorial n = Nat.factorial 98 * 9900 := by
          linarith [heq]
        nlinarith [Nat.factorial_pos 98, heq]
      nlinarith [Nat.factorial_pos 98, heq]
    have eq7 : n ≤ 100 := by
      by_contra h
      push_neg at h
      have eq8 : n ≥ 101 := by omega
      have heq4 : Nat.factorial n ≥ Nat.factorial 101 := by
        apply Nat.factorial_le
        omega
      have heq2 : Nat.factorial n < Nat.factorial 101 := by
        have eq7 : Nat.factorial n = Nat.factorial 98 * 9900 := by
          linarith [heq]
        have heq3 : Nat.factorial 98 * 9900 < Nat.factorial 101 := by
          norm_num [Nat.factorial]
        have eq8 : Nat.factorial n = Nat.factorial 98 * 9900 := by
          linarith [heq]
        omega
      linarith
    have eq8 : n = 100 := by
      have eq9 : n ≤ 100 := by omega
      have eq10 : n ≥ 99 := by omega
      interval_cases n <;> try { contradiction } <;> try { trivial }
    exact eq8
  constructor
  · -- Proof of (c): ∀ m, m > 0 ∧ Nat.factorial (m + 2) / Nat.factorial m = 40200 → m = 199
    intro m h
    rcases h with ⟨hm_pos, heq⟩
    have h15 : Nat.factorial (m + 2) / Nat.factorial m = (m + 2) * (m + 1) := by
      have h14 : Nat.factorial (m + 2) = (m + 2) * (m + 1) * Nat.factorial m := by
        simp [Nat.factorial]
        all_goals ring
      have h144 : Nat.factorial (m + 2) / Nat.factorial m = (m + 2) * (m + 1) := by
        rw [h14]
        field_simp
        all_goals omega
      exact h144
    rw [h15] at heq
    have eq35 : m = 199 := by
      nlinarith [sq_nonneg (m - 199 : ℕ), sq_nonneg ((m : ℕ) + 1 - 200), sq_nonneg ((m : ℕ) + 2 - 201)]
    exact eq35
  · -- Proof of (d): ∀ q, 0 < q → ∀ r, Nat.factorial (q + 2) - Nat.factorial (q + 1) = Nat.factorial q * r → IsSquare r
    intro q hq r heq
    have eq1 : Nat.factorial (q + 2) - Nat.factorial (q + 1) = Nat.factorial (q + 1) * (q + 1) := by
      have h1 : Nat.factorial (q + 2) = (q + 2) * Nat.factorial (q + 1) := by
        simp [Nat.factorial]
      rw [h1]
      cases q with
      | zero => linarith
      | succ q =>
        simp [Nat.factorial]
        all_goals
          ring_nf
          <;> omega
    have h33 : Nat.factorial (q + 1) * (q + 1) = Nat.factorial q * r := by
      nlinarith [heq, eq1]
    have h4 : Nat.factorial (q + 1) = (q + 1) * Nat.factorial q := by
      simp [Nat.factorial]
    rw [h4] at h33
    have h7 : r = (q + 1) ^ 2 := by
      have h5 : Nat.factorial q > 0 := by
        apply Nat.factorial_pos
      nlinarith [show Nat.factorial q ≥ 1 by linarith [Nat.factorial_pos q]]
    have h6 : IsSquare r := by
      rw [h7]
      exact ⟨q + 1, by ring⟩
    exact h6