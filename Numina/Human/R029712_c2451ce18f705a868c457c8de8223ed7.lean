import Mathlib

/- Soit $\mathrm{a}, \mathrm{b}, \mathrm{c} \geqslant 1$ des entiers tels que $\mathrm{a}^{\mathrm{b}} \mid \mathrm{b}^{\mathrm{c}}$ et $\mathrm{a}^{\mathrm{c}} \mid \mathrm{c}^{\mathrm{b}}$. Montrer que $\mathrm{a}^{2} \mid \mathrm{bc}$. -/
theorem number_theory_607372
    (a b c : ℕ)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hc : 1 ≤ c)
    (h1 : a ^ b ∣ b ^ c)
    (h2 : a ^ c ∣ c ^ b) :
    a ^ 2 ∣ b * c := by
  -- change the form of the h1
  rw [<-Nat.factorization_le_iff_dvd] at h1 h2
  repeat rw [Nat.factorization_pow] at h1
  repeat rw [Nat.factorization_pow] at h2
  -- show that 2 • a.factorization ≤ b.factorization + c.factorization
  . have h (p : ℕ) (hp : Nat.Prime p) : b * c * ((2 • a.factorization) p) ^ 2 ≤ b * c * ((b.factorization + c.factorization) p) ^ 2 := by
      calc
        b * c * ((2 • a.factorization) p) ^ 2 = 4 * ((b • a.factorization) p) * ((c • a.factorization) p) := by field_simp; ring_nf
        -- combine the two inequalities
        _ ≤ 4 * ((c • b.factorization) p) * ((b • c.factorization) p) := by
          apply mul_le_mul
          rw [Finsupp.le_def] at h1 h2
          linarith only [h1 p]
          linarith only [h2 p]
          all_goals positivity
        _ = b * c * (4 * b.factorization p * c.factorization p) := by field_simp; ring_nf
        -- show that 4 * b.f * c.f ≤ (b.f + c.f) ^ 2
        _ ≤ b * c * (b.factorization p + c.factorization p) ^ 2 := by
          rify
          ring_nf
          linarith only [show 0 ≤ (b : ℝ) * c * ((b.factorization p : ℝ) - (c.factorization p : ℝ)) ^ 2 by positivity]
        _ = b * c * ((b.factorization + c.factorization) p) ^ 2 := by rw [Finsupp.add_apply]
    -- cancel b * c of inequality
    replace h (p : ℕ) (hp : Nat.Prime p) : ((2 • a.factorization) p) ^ 2 ≤ ((b.factorization + c.factorization) p) ^ 2 := by
      replace h := h p hp
      apply Nat.le_of_mul_le_mul_left at h
      apply h
      positivity

    -- show that ∀ p, 2 • a.factorization p ≤ (b.factorization + c.factorization) p
    replace h (p : ℕ) (hp : Nat.Prime p) : (2 • a.factorization) p ≤ (b.factorization + c.factorization) p := by
      replace h := h p hp
      apply nonneg_le_nonneg_of_sq_le_sq
      positivity
      ring_nf at h ⊢
      exact h

    -- show that a ^ 2 ∣ b * c
    rw [<-Nat.factorization_mul] at h
    rw [<-Nat.factorization_pow] at h
    rw [Nat.factorization_prime_le_iff_dvd] at h
    exact h
    -- condition of positivity
    all_goals positivity
  all_goals positivity
