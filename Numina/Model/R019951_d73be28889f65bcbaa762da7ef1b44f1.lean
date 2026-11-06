import Mathlib


theorem number_theory_6620 (x : ℕ) (hx : x > 0) : (10^10^x) % 7 = 4 := by
  have h1 : ∀ (x : ℕ), x > 0 → (10 ^ (10 ^ x)) % 7 = 4 := by
    intro x hx
    induction x with
    | zero => linarith
    | succ x ih =>
      cases x with
      | zero => 
        norm_num 
      | succ x => 
        have h2 : (10 ^ (10 ^ (x + 1 + 1))) % 7 = 4 := by
          have h3 : (10 ^ (10 ^ (x + 1 + 1))) = (10 ^ (10 ^ (x + 1)) ) ^ 10 := by
            ring_nf
          rw [h3]
          simp [Nat.pow_mod, ih]
        exact h2
  specialize h1 x hx 
  simpa using h1