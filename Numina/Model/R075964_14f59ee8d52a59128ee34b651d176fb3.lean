import Mathlib

theorem number_theory_187808 :
    ∀ a b : ℕ, (Even a ∧ Even b → Even (a * b)) ∧
    (Odd a ∧ Odd b → Odd (a * b)) ∧
    (Even a ∧ Odd b → Even (a * b)) ∧
    (Odd a ∧ Even b → Even (a * b)) := by 
  intro a b
  constructor
  · -- Proof that if a and b are even, then a * b is even
    intros h
    rcases h with ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    use 2 * m * n
    rw [hm, hn]
    ring_nf
  constructor
  · -- Proof that if a and b are odd, then a * b is odd
    intros h
    rcases h with ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    use 2 * m * n + m + n 
    rw [hm, hn]
    ring_nf
  constructor
  · -- Proof that if a is even and b is odd, then a * b is even
    intros h
    rcases h with ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    use 2 * m * n + m 
    rw [hm, hn]
    ring_nf
  · -- Proof that if a is odd and b is even, then a * b is even
    intros h
    rcases h with ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    use 2 * m * n + n 
    rw [hm, hn]
    ring_nf