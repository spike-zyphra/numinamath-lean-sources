import Mathlib

def S : ℕ → ℕ
| n => ∑ i in Finset.Icc 1 n, Nat.factorial i

theorem number_theory_214688 :
    ∃ n, ∃ p, p.Prime ∧ p > 10^2012 ∧ p ∣ S n := by
  -- Use n = 0.
  use 0
  -- Need to prove ∃ p, p.Prime ∧ p > 10^2012 ∧ p ∣ S 0
  -- But S 0 is the empty sum, which is 0.
  -- We need a prime p > 10^2012 dividing 0, which is trivial since all primes divide 0.
  have h2 := Nat.exists_infinite_primes (10 ^ 2012 + 1)
  rcases h2 with ⟨p, hp1, hp2⟩
  use p
  constructor
  · exact hp2
  constructor
  · -- Show p > 10 ^ 2012
    have h3 : 10 ^ 2012 + 1 ≤ p := hp1
    omega
  · simp [S, Finset.sum_eq_zero]
    <;> try { norm_num }
    <;> try { tauto }
  all_goals tauto
  all_goals try { 
    rw [Nat.dvd_iff_mod_eq_zero]
    simp
    try { 
      have h2 := Nat.exists_infinite_primes (10 ^ 2012 + 1)
      rcases h2 with ⟨p, hp1, hp2⟩
      tauto
    }
  }
  all_goals try { 
    norm_num
    <;> try { tauto }
    <;> try { 
      have h2 := Nat.exists_infinite_primes (10 ^ 2012 + 1)
      rcases h2 with ⟨p, hp1, hp2⟩
      tauto
    }
  }
  all_goals try { 
    tauto 
    <;> try { 
      have h2 := Nat.exists_infinite_primes (10 ^ 2012 + 1)
      rcases h2 with ⟨p, hp1, hp2⟩
      tauto
    }
  }