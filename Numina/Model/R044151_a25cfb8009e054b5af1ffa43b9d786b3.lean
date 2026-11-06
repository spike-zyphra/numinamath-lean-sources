import Mathlib

open BigOperators

theorem number_theory_4862 : ∀ (n : ℕ),
    ∑ m in Finset.filter (fun x => x ∣ n) (Finset.range (Nat.succ n)), Nat.totient m = n := by
  intro n
  by_cases hn : n = 0
  · -- If n = 0
    rw [hn]
    simp
  · -- When n ≠ 0
    have hn' : n ≠ 0 := by
      intro h
      apply hn
      all_goals omega
    have h1 : Finset.filter (fun x => x ∣ n) (Finset.range (n + 1)) = n.divisors := by 
      ext x
      simp [Nat.mem_divisors, hn']
      <;> try { 
        omega 
      }
    rw [h1]
    rw [Nat.sum_totient]