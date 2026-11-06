import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem number_theory_3400 : IsGreatest {n : ℕ | ∃ k : ℕ, n > 0 ∧ k > 0 ∧ (Nat.factorial 20) = 18^n * k} 4 := by
  constructor
  · -- Show 4 is in the set
    use (Nat.factorial 20) / (18 ^ 4)
    all_goals
      native_decide
  · -- Show that for all $n$ in the set, $n \leq 4$.
    intro n hn
    rcases hn with ⟨k, hn_pos, hk_pos, heq⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 5 := by omega
    have h2 : (18 : ℕ) ^ 5 ∣ Nat.factorial 20 := by
      have h3 : (18 : ℕ) ^ n ∣ Nat.factorial 20 := by
        use (k)
        all_goals nlinarith
      have h4 : n ≥ 5 := h1
      have h5 : (18 : ℕ) ^ 5 ∣ (18 : ℕ) ^ n := by
        apply pow_dvd_pow _ (by omega)
      have h6 : (18 : ℕ) ^ 5 ∣ (Nat.factorial 20) := by
        exact dvd_trans h5 h3
      assumption
    have h7 : ¬ (18 ^ 5 ∣ Nat.factorial 20) := by
      norm_num [Nat.factorial]
    exact h7 h2