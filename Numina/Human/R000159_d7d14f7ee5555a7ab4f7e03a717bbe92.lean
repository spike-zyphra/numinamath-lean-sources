import Mathlib

/- 3. Show that if $n$ is an Euler pseudoprime to the bases $a$ and $b$, then $n$ is an Euler pseudoprime to the base $a b$.

The text is already in English, so no translation is needed. -/
theorem number_theory_5209 {n a b : ℕ} (ha : Nat.Coprime a n) (hb : Nat.Coprime b n)
    (h1 : ∀ x, a * x ≡ x [MOD n]) (h2 : ∀ x, b * x ≡ x [MOD n]) :
    ∀ x, a * b * x ≡ x [MOD n] := by 
  intro x
  simp_all [Nat.ModEq, Nat.ModEq, Nat.ModEq]
  <;> simp_all [mul_assoc]
