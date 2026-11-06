import Mathlib

theorem number_theory_74710 {n : ℕ} (hn : n ≠ 0) :
    ∑ d in n.divisors, d = 28 ↔ n = 12 := by
  constructor
  · -- Forward direction: If the sum of divisors is 28, then n = 12.
    intro h
    have h1 : n ≤ 28 := by
      have h2 : n ∣ n := by
        exact dvd_refl n
      have h3 : n ∈ n.divisors := by
        exact Nat.mem_divisors.mpr ⟨h2, by omega⟩
      have h4 : n ≤ ∑ d in n.divisors, d := by
        apply Finset.single_le_sum (fun x _ => by positivity) h3
      rw [h] at h4
      all_goals linarith
    interval_cases n <;> try { contradiction }
      <;> try { native_decide }
  · -- Backward direction: If n = 12, then the sum of divisors is 28.
    intro h_eq
    rw [h_eq]
    native_decide