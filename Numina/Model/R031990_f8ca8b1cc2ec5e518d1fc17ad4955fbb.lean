import Mathlib

theorem number_theory_23490 : ∃ (A : Finset ℕ), A = {n : ℕ | (Nat.digits 5 n).length = 3 ∧ (Nat.digits 8 n).length = 2} ∧ ((∑ n ∈ A, n) : ℚ) / A.card = 44 := by
  use Finset.Icc 25 63
  constructor
  · -- Show that Finset.Icc 25 63 equals the given set definition
    ext n
    simp
    constructor
    · -- Assume n is in Finset.Icc 25 63, need to show it's in the given set.
      rintro ⟨h₁, h₂⟩
      constructor
      · -- Show that (Nat.digits 5 n).length = 3.
        have h3 : n ≥ 25 := by linarith
        have h4 : n ≤ 63 := by linarith
        interval_cases n <;> norm_num
      · -- Show that (Nat.digits 8 n).length = 2
        have h3 : n ≥ 25 := by linarith
        have h4 : n ≤ 63 := by linarith
        interval_cases n <;> norm_num
    · -- Assume n is in the given set, need to show it is in Finset.Icc 25 63.
      rintro ⟨h1, h2⟩
      constructor
      · -- Show n ≥ 25
        by_contra h
        push_neg at h
        interval_cases n <;> norm_num at h1 h2
      · -- Show n ≤ 63
        by_contra h
        push_neg at h
        have h3 : n ≥ 64 := by omega
        have h4 : (Nat.digits 8 n).length > 2 := by
          have h5 : (Nat.digits 8 n).length = Nat.log 8 n + 1 := by
            rw [Nat.digits_len]
            all_goals omega
          rw [h5]
          have h6 : Nat.log 8 n ≥ 2 := by
            apply Nat.le_log_of_pow_le (by omega)
            all_goals omega
          omega
        omega
  · -- Show that the average is 44
    native_decide