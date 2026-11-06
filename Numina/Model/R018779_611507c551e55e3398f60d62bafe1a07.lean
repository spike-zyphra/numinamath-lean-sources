import Mathlib

theorem number_theory_7010 (p : ℕ) (hp : Nat.Prime p) (l : ℕ) (hl : 1 ≤ l) :
    p ^ (l - 1) * (p - 1) = (p ^ l).totient := by
  have h1 : (p ^ l).totient = p ^ (l - 1) * (p - 1) := by
    have h4 : p.Prime := hp
    have h5 : ∀ (j : ℕ), (p ^ (j + 1)).totient = p ^ j * (p - 1) := by
      intro j 
      rw [Nat.totient_prime_pow h4 (by linarith)]
      <;> 
      cases j with
      | zero => 
        simp
      | succ j => 
        simp [Nat.pow_add] at *
        <;> ring_nf
        all_goals try { tauto } 
    have h6 : l ≥ 1 := by linarith 
    have h7 : (p ^ l).totient = p ^ (l - 1) * (p - 1) := by 
      have h8 : l = (l - 1) + 1 := by 
        omega 
      rw [h8] 
      have h10 : (p ^ ((l - 1) + 1)).totient = p ^ (l - 1) * (p - 1) := h5 (l - 1)
      exact h10 
    exact h7 
  linarith [h1]