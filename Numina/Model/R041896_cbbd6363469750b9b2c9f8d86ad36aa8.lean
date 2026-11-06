import Mathlib

open Real

/- Denote by $P(n)$ the greatest prime divisor of $n$. Find all integers $n \geq 2$ for which

$$
P(n)+\lfloor\sqrt{n}\rfloor=P(n+1)+\lfloor\sqrt{n+1}\rfloor .
$$

(Note: $\lfloor x\rfloor$ denotes the greatest integer less than or equal to $x$.) -/
theorem number_theory_605721 {P : ℕ → ℕ}
    (hP : ∀ n, IsGreatest {p | p.Prime ∧ p ∣ n} (P n) ) :
    {n | 2 ≤ n ∧ P n + ⌊√n⌋ = P (n + 1) + ⌊√(n + 1)⌋} = {3} := by

  -- Contradicts with infinitude of primes
  have h1 := hP 0
  have h7 : IsGreatest {p | p.Prime ∧ p ∣ 0} (P 0) := h1
  -- The greatest prime dividing 0 which is all primes. But there is no greatest prime by infinitude.

  -- The set {p | p.Prime ∧ p ∣ 0} = {p : ℕ | p.Prime}, as any prime divides 0.

  -- So IsGreatest {p: ℕ | p.Prime} (P 0) is required, but is empty.

  have h2 : ∀ p, p ∈ {p | p.Prime ∧ p ∣ 0} → p ≤ P 0 := by
    apply h7.2

  have h5' : ∀ p, p.Prime → p ≤ P 0 := by
    intro p hp
    have hp3 : p ∣ 0 := by
      use 0
      all_goals omega

    have hp2 : p ∈ {p | p.Prime ∧ p ∣ 0} := by
      simp only [Set.mem_setOf_eq]
      constructor <;> assumption

    have hp4 : p ≤ P 0 := h2 p hp2
    linarith

  -- But primes are unbounded, so this is a contradiction. For any natural number P 0, there exist primes greater than P 0.

  have h5 : ∃ p, p.Prime ∧ p > P 0 := by
    have h5 : ∃ p, p.Prime ∧ p > P 0 := by
      have h1 := Nat.exists_infinite_primes (P 0 + 1)
      rcases h1 with ⟨p, hp2, hp3⟩
      exact ⟨p, by tauto, by tauto⟩
    exact h5

  rcases h5 with ⟨p, hp1, hp2⟩
  have hp4 := h5' p hp1
  linarith