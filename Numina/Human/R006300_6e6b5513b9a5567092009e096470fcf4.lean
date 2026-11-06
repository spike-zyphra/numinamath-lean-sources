import Mathlib

/-
Let $k$ be an odd positive natural number. Let $N$ be a natural number such that $N$ is odd and $N$ is divisible by $k$. Determine the remainder when $N$ is divided by $2k$. Show that this remainder is $k$.
-/

theorem number_theory_635662 (k : ℕ) (hk : Odd k ∧ 0 < k) (N : ℕ) (hN : Odd N ∧ k ∣ N):
  N % (2 * k) = k := by
  obtain ⟨ok, kpos⟩ := hk
  obtain ⟨oN, kdn⟩ := hN

  --Asssue that dk = N. We have that d is odd.
  obtain ⟨d, hd⟩ := kdn
  have od : Odd d := by 
    by_contra nod
    have ed : Even d := by exact Nat.not_odd_iff_even.mp nod
    have : Even (k * d) := by exact Even.mul_left ed k
    rw [← hd] at this
    have : ¬ Odd N := by exact Nat.not_odd_iff_even.mpr this
    contradiction

  --Assume that d = 2*l+1, and hence N = (2l+1)*k.
  obtain ⟨l,hl⟩ := od
  rw [hl] at hd
  rw [hd]
  rw [mul_add]
  rw [Nat.add_mod]
  refine Nat.mod_eq_of_modEq ?_ ?_
  simp

  --Putting in the value of N, we get our claim.
  have e1 : k * (2 * l) % (2 * k) ≡ 0 [MOD (2*k)] := by    
    ring_nf
    have : (k*2) ∣ k*l*2 := by use l; ring
    have : k * l * 2 % (k * 2) = 0:= by exact Nat.dvd_iff_mod_eq_zero.mp this
    rw [this]
  have e2 : k * 1 % (2 * k) ≡ k [MOD 2 * k] := by 
    simp
    exact Nat.mod_modEq k (2 * k)
  have : k * (2 * l) % (2 * k) + (k * 1 % (2 * k)) ≡ 0 + k [MOD 2 * k] := by exact Nat.ModEq.add e1 e2
  simp at this
  exact this
  omega
  
