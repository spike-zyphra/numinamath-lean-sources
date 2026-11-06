import Mathlib


lemma bezout_identity {a b : ℕ} (h : Nat.gcd a b = 1) :
  ∃ x y : ℤ, a * x + b * y = 1 := by 
  use (Int.gcdA a b), (Int.gcdB a b)
  rw [←Int.gcd_eq_gcd_ab]
  simp
  exact h

theorem number_theory_637201 {f : ℤ → ℤ} (hf : ∀ x, f x = 3 * x + 2) (K D : ℕ)
  (hK : K > 0) (hD : D > 0) (hCD : Nat.gcd 3 D = 1) :
  ∃ m, ↑D ∣ f^[K] m := by 
  -- prove the general formula for f 
  have h1 : ∀ k, f^[k] = fun x => 3 ^k * x + 3 ^ k - 1 := by 
    intro k
    induction k with 
    | zero => 
      simp
      funext x
      simp
    | succ k ih => 
      conv => 
        simp [hf, ih]
      funext x
      simp
      rw [hf]
      ring_nf
  rw [h1]
  simp
  have h2 : Nat.gcd (3 ^ K) D = 1 := by 
    exact Nat.Coprime.pow_left K hCD
  obtain ⟨x, y, hxy⟩ := bezout_identity h2
  use (-x * (3 ^ K - 1))
  have aux1 : 3 ^ K * x = 1 - D * y := by 
    have aux : ((3 : ℕ) ^ K : ℕ) = (3 : ℤ) ^ K := by 
      norm_cast
    rw [aux] at hxy
    linarith
  
  have aux2 : 3 ^ K * (-x * (3 ^ K - 1))  = 
    - (3 ^ K * x) * (3 ^ K - 1) := by 
    ring
  rw [aux2, aux1]
  use (y * (3 ^ K - 1))
  ring