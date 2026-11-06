import Mathlib

/-- A rectangle with positive integer side lengths in cm has area A cm2 and perimeter P cm. Which
of the following numbers cannot equal A+P?
(A) 100(B) 102(C) 104(D) 106(E) -/
theorem number_theory_95212 {A P a b: ℕ} (ha : a > 0) (hb : b > 0)
    (hA' : A = a * b) (hP' : P = 2 * (a + b)) :
    A + P ≠ 102 := by {

  -- We plug in the formulae for area and circumference and assume equality with the aim of showing
  -- a contradiction in the hypotheses
  rw [hA',hP']
  intro hEq

  -- We show by simple rearranging that this implies (a + 2) * (b + 2) = 106. This is impossible
  -- because 106 = 53 * 2 and 53 is a prime, so a or b would have to be 0, which we excluded in the
  -- assumptions.
  have h₁ : (a + 2) * (b + 2) = 106 := by {
    calc (a + 2) * (b + 2) = a * b + 2 * (a + b) + 4 := by ring
                         _ = 102 + 4 := by rw [hEq]
                         _ = 106 := by norm_num
  }

  -- We show that a + 2 has to be a divisor of 106 and thus ∈ {1, 2, 53, 106}
  have h₂ : (a + 2) ∈ ({1, 2, 53, 106} : Finset ℕ) := by {
    have : (a + 2) ∈ Nat.divisors 106 := by {
      rw [Nat.mem_divisors]
      constructor
      use (b + 2)
      exact h₁.symm
      trivial
    }
    exact this
  }
  -- Here we already exclude a + 2 = 1 trivially
  simp at h₂

  -- We now split into the remaining cases
  rcases h₂ with ha0 | ha51 | ha104

  -- a = 0 immediately contradicts the hypotheses
  rw [ha0] at ha
  trivial

  -- a = 51 implies b = 0, contradicting our hypotheses.
  rw [ha51] at h₁
  norm_num at h₁
  suffices : 106 < 106
  trivial

  calc 106 = 53 * (0 + 2) := by norm_num
        _  < 53 * (b + 2) := by linarith -- uses 0 < b by assumption
        _ = 106 := by exact h₁

  -- a = 104 can be excluded easily because then b + 2 = 1
  rw [ha104] at h₁
  norm_num at h₁
  linarith -- shows that b + 2 can't be = 1.
}