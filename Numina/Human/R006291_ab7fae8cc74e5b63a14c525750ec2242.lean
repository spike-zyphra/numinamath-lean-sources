import Mathlib

/- Let $A$ be a positive integer coprime to $10$. Let $X$ be a positive integer, and let $D$ be a positive integer. Show that there exists an integer $K > X$ such that $A^K \equiv A^X \pmod{10^D}$. -/
theorem number_theory_635581 (A : ℕ) (hA₀ : 0 < A) (hA : A.Coprime 10) (X D : ℕ) (hX₀ : 0 < X) (hD₀ : 0 < D) :
    ∃ K > X, A ^ K ≡ A ^ X [MOD 10 ^ D] := by
  -- Since A is coprime to 10, A ^ (10 ^ D).totient ≡ 1 [MOD 10 ^ D].
  -- We set K = X + (10 ^ D).totient.
  use X + (10 ^ D).totient
  have hA₁ : A ^ (10 ^ D).totient ≡ 1 [MOD 10 ^ D] := Nat.ModEq.pow_totient (Nat.Coprime.pow_right D hA)
  simp [pow_add]
  nth_rw 2 [show A ^ X = A ^ X * 1 by simp]
  exact Nat.ModEq.mul_left _ hA₁