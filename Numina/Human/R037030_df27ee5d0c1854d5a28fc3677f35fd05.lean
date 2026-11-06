import Mathlib

/- Prove that if the number $n!+1$ is divisible by $n+1$, then $n+1$ is a prime number.

# -/
theorem number_theory_217834 (n : ℕ) (h : n > 0) :
    (n + 1) ∣ Nat.factorial n + 1 → Nat.Prime (n + 1) := by
  rintro hn
  -- prove by contradiction assume, n+1 is not prime (and obivously not 0 or 1)
  by_contra hc
  have : n + 1 ≥ 2 := by omega
  -- then n+1 has a proper divisor x
  obtain ⟨x, hxdvd, hx1, hxn⟩ := Nat.exists_dvd_of_not_prime this hc
  -- x ≤ n and x ≠ 0
  have : x ≤ n := by
    have : x ≤ n + 1 := by
      apply Nat.le_of_dvd
      positivity
      assumption
    omega
  have : x ≠ 0 := by
    by_contra hxz
    rw [hxz] at hxdvd
    simp at hxdvd
  -- so x divides n!
  have hd₁ : x ∣ n.factorial := by
    apply Nat.dvd_factorial
    positivity
    assumption
  -- but x also divides n!+1
  have hd₂ : x ∣ n.factorial + 1 := by calc
    x ∣ n + 1 := by assumption
    _ ∣ n.factorial + 1 := by assumption
  -- hence x divides 1 but that is contradiction
  have : x ∣ (n.factorial + 1) - n.factorial := by
    refine Nat.dvd_sub ?_ hd₂ hd₁
    simp
  simp at this
  contradiction