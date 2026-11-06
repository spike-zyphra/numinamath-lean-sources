import Mathlib

theorem number_theory_109874 : {n : ℕ | 100 < Real.sqrt n ∧ Real.sqrt n < 101}.encard = 200 := by
  have h2 : {n : ℕ | 100 < Real.sqrt n ∧ Real.sqrt n < 101} = Set.Icc 10001 10200 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Nat.cast_ofNat]
    constructor
    · -- Assume 100 < sqrt n ∧ sqrt n < 101, prove 10001 ≤ n ∧ n ≤ 10200
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : (n : ℝ) ≥ 0 := by positivity
      have h4 : 100 < Real.sqrt (↑n) := by linarith
      have h5 : Real.sqrt (↑n) < 101 := by linarith
      have h6 : (100 : ℝ) ^ 2 < (Real.sqrt (↑n) : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (↑n), Real.sqrt_nonneg (↑n)]
      have h7 : (Real.sqrt (↑n) : ℝ) ^ 2 < (101 : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (↑n), Real.sqrt_nonneg (↑n)]
      have h8 : (Real.sqrt (↑n) : ℝ) ^ 2 = (↑n : ℝ) := by
        rw [Real.sq_sqrt]
        have h9 : (↑n : ℝ) ≥ 0 := by positivity
        linarith
      have h9 : (10000 : ℝ) < (↑n : ℝ) := by
        nlinarith
      have h10 : (↑n : ℝ) < (10201 : ℝ) := by
        nlinarith
      have h11 : 10000 < n := by
        by_contra h
        push_neg at h
        have h12 : n ≤ 10000 := by omega
        have h13 : (↑n : ℝ) ≤ (10000 : ℝ) := by exact_mod_cast h12
        linarith
      have h12 : n < 10201 := by
        by_contra h
        push_neg at h
        have h13 : n ≥ 10201 := by omega
        have h14 : (↑n : ℝ) ≥ (10201 : ℝ) := by exact_mod_cast h13
        linarith
      constructor
      · -- Show that 10001 ≤ n
        omega
      · -- Show that n ≤ 10200
        omega
    · -- Assume 10001 ≤ n ∧ n ≤ 10200, prove 100 < sqrt n ∧ sqrt n < 101
      rintro ⟨h1, h2⟩
      have h3 : (↑n : ℝ) ≥ 0 := by positivity
      have h4 : (10000 : ℝ) < (↑n : ℝ) := by exact_mod_cast show (10000 : ℕ) < n by omega
      have h5 : (↑n : ℝ) < (10201 : ℝ) := by exact_mod_cast show (n : ℕ) < (10201 : ℕ) by omega
      have h6 : (100 : ℝ) ^ 2 < (↑n : ℝ) := by
        nlinarith
      have h7 : (↑n : ℝ) < (101 : ℝ) ^ 2 := by
        nlinarith
      have h8 : 100 < Real.sqrt (↑n) := by
        nlinarith [Real.sqrt_nonneg (↑n), Real.sq_sqrt (show 0 ≤ (↑n : ℝ) by linarith), sq_nonneg (Real.sqrt ↑n - 100)]
      have h9 : Real.sqrt (↑n) < 101 := by
        nlinarith [Real.sqrt_nonneg (↑n), Real.sq_sqrt (show 0 ≤ (↑n : ℝ) by linarith), sq_nonneg (Real.sqrt ↑n - 101)]
      constructor
      · exact_mod_cast h8
      · exact_mod_cast h9
  rw [h2]
  rw [Set.encard]
  simp
  <;> try { native_decide }