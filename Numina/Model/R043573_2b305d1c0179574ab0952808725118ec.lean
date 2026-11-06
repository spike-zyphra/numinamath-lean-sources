import Mathlib

theorem number_theory_113226 (a : ℕ → ℕ)
    (ha : ∀ n, a n = ∑ i in Finset.Icc 1 n, i ^ i) :
    ∀ N, ∃ n, n > N ∧ Odd (a n) := by
  intro N
  have h1 : ∀ (n : ℕ), a n = ∑ i in Finset.Icc 1 n, i ^ i := by 
    intro n
    specialize ha n
    simpa using ha
  use 4 * N + 1
  constructor
  · -- Show that 4N + 1 > N
    omega
  · -- Show that a_{4N + 1} is odd
    rw [h1 (4 * N + 1)]
    have h3 : (∑ i in Finset.Icc 1 (4 * N + 1), i ^ i) % 2 = 1 := by
      have h4 : ∀ (N : ℕ), (∑ i in Finset.Icc 1 (4 * N + 1), i ^ i) % 2 = 1 := by
        intro N
        induction N with
        | zero =>
          norm_num [Finset.sum_Icc_succ_top]
        | succ k hk =>
          rw [show 4 * (k + 1) + 1 = (4 * k + 1) + 4 by ring]
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [Finset.sum_Icc_succ_top (by linarith)]
          simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
          all_goals 
            omega
      specialize h4 N
      simpa using h4
    have h4 : (∑ i in Finset.Icc 1 (4 * N + 1), i ^ i) % 2 = 1 := h3
    have : Odd (∑ i in Finset.Icc 1 (4 * N + 1), i ^ i) := by 
      rw [Nat.odd_iff]
      have h5 : (∑ i in Finset.Icc 1 (4 * N + 1), i ^ i) % 2 = 1 := h4 
      omega 
    exact this