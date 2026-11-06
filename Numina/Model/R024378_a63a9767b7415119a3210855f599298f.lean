import Mathlib

def A : Set ℕ := {n * (n + 1) | n > 0}
def B : Set ℕ := {3 * m - 1 | m > 0}

theorem number_theory_297884 :
    ∃ a : ℕ → ℕ, (∀ k, a k ∈ A ∩ B) ∧
      (∀ k, a k = 9 * k ^ 2 - 9 * k + 2) := by
  use fun k => 9 * k ^ 2 - 9 * k + 2
  constructor
  · -- Show that for all k, a_k ∈ A ∩ B
    intro k
    have h1 : 9 * k ^ 2 - 9 * k + 2 ∈ A ∩ B := by
      constructor
      · -- Show that 9k^2 - 9k + 2 ∈ A
        cases k with
        | zero =>
          simp [A]
          <;> try { 
            use 1 
            all_goals try { 
              norm_num 
              <;> try { 
                tauto 
              } 
            } 
          }
        | succ k =>
          simp [A]
          use 3 * (k + 1) - 2
          cases k with
          | zero =>
            all_goals try { 
              simp [Nat.mul_add, Nat.add_mul, pow_two]
              <;> try { 
                omega 
              } 
            }
          | succ k =>
            simp [Nat.mul_add, Nat.add_mul, pow_two]
            <;> try { 
              ring_nf 
              <;> try { 
                omega 
              } 
            }
      · -- Show that 9k^2 - 9k + 2 ∈ B
        simp [B]
        use ( (9 * k ^ 2 - 9 * k + 2 + 1) / 3 )
        cases k with
        | zero =>
          all_goals try { 
            simp 
            <;> try { 
              norm_num 
              <;> try { 
                tauto 
              } 
            } 
          }
        | succ k =>
          simp [Nat.mul_add, Nat.add_mul, pow_two]
          all_goals try { 
            ring_nf 
            <;> try { 
              omega 
            } 
          }
    tauto
  · -- Show that for all k, a_k = 9 * k ^ 2 - 9 * k + 2
    intro k
    rfl