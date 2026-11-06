import Mathlib

theorem number_theory_6102 (a b c m : ℤ) (hcop : c.gcd m = 1) :
    c * a ≡ c * b [ZMOD m] ↔ a ≡ b [ZMOD m] := by

  constructor
  · -- Forward direction: Assume $c a \equiv c b \pmod{m}$, prove $a \equiv b \pmod{m}$

    intro h

    have h1 : m ∣ c * b - c * a := by
      exact Int.ModEq.dvd h

    have h2 : IsCoprime m c := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simp [Int.gcd_comm, hcop]

    have h3 : m ∣ b - a := by 
      have h4 : m ∣ c * (b - a) := by 
        -- because $c * b - c * a = c * (b - a)$
        have eq1 : c * b - c * a = c * (b - a) := by 
          ring
        rw [eq1] at h1
        exact h1
      have h5 : m ∣ b - a := by 
        apply IsCoprime.dvd_of_dvd_mul_left h2 h4
      exact h5

    exact Int.modEq_of_dvd h3

  · -- Backward direction: Assume $a \equiv b \pmod{m}$, prove $c a \equiv c b \pmod{m}$

    intro h

    exact Int.ModEq.mul_left c h