import Mathlib

/- A number N_k is defend as periodic if it's composed in number base N of a repeated k times/ Prove that 7 divides to infinite periodic numbers of the set 
N1 N2...-/
def N (k : ℕ) := ∑ i ∈ Finset.range k, 10 ^ i

theorem number_theory_57655 :
    ∀ n, ∃ m, m > n ∧ 7 ∣ N m := by
  intro n
  use 6 * ((n + 6) / 6)
  constructor
  · -- We need to prove m > n, i.e., 6 * ((n + 6) / 6) > n
    omega
  · -- We need to prove 7 ∣ N (6 * ((n + 6) / 6))
    have h1 : N (6 * ((n + 6) / 6)) = (10 ^ (6 * ((n + 6) / 6)) - 1) / 9 := by
      rw [N]
      have h1 : ∀ k, ∑ i in Finset.range k, 10 ^ i = (10 ^ k - 1) / 9 := by
        intro k 
        induction k with
        | zero => 
          simp 
        | succ k ih => 
          rw [Finset.sum_range_succ, ih]
          simp [pow_succ]
          <;> omega 
      simp [h1]
    rw [h1]
    have h2 : (10 ^ (6 * ((n + 6) / 6)) - 1) / 9 % 7 = 0 := by 
      have h10 : (10 : ℕ) ^ 6 % 63 = 1 := by norm_num
      have h11 : (10 : ℕ) ^ (6 * ((n + 6) / 6)) % 63 = 1 := by 
        have h103 : (10 : ℕ) ^ (6 * ((n + 6) / 6)) = 
          ((10 ^ 6) ^ ((n + 6) / 6)) := by 
          rw [pow_mul]
        rw [h103]
        rw [Nat.pow_mod]
        simp [h10]
      have h63 : (10 ^ (6 * ((n + 6) / 6)) - 1) / 9 % 7 = 0 := by
        have h105 : (10 : ℕ) ^ (6 * ((n + 6) / 6)) % 63 = 1 := h11
        omega
      exact h63
    exact Nat.dvd_of_mod_eq_zero h2