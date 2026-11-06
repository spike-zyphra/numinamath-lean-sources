import Mathlib

theorem number_theory_239123 {m : ℕ} (hm : 1 ≤ m) (a : ℕ) (ha : 0 < a) (ha' : a.gcd m = 1) :
    a ^ m.totient ≡ 1 [MOD m] := by 
  have h2 : a ^ m.totient ≡ 1 [MOD m] := by
    apply Nat.ModEq.pow_totient
    exact ha'
  simpa [Nat.ModEq] using h2