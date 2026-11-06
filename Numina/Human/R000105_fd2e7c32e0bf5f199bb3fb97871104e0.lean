import Mathlib

/- Fermat number -/
def f_4615 (n : ℕ) := 2^(2^n) + 1

/- Use the fact that every prime divisor of \( F_{4} = 2^{2^{4}} + 1 = 65537 \) is of the form \( 2^{6} k + 1 = 64k + 1 \) to verify that \( F_{4} \) is prime. You should need only one trial division.-/
theorem  number_theory_4615
 (pf : ∀ k, 64 * k + 1 = 65537 → Prime (64 * k + 1))
    (Ph : ∀ F : ℕ → Prop, ((∃ p : ℕ, ∀ k : ℕ, (p : ℕ) = 64 * k + 1 → p ∣ 65537 ∧ Prime p))) :
    Nat.primeFactorsList (f_4615 4)=[65537] := by
  -- verify by computation
  simp [f_4615]
  unfold Nat.primeFactorsList
  simp
  norm_num
