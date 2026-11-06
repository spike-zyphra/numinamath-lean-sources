import Mathlib

open Real

theorem inequalities_601750 :
    (∀ p q : ℝ, p^2 + q^2 + 1 > p * (q + 1)) ∧
    (∀ b : ℝ, (∀ p q : ℝ, p^2 + q^2 + 1 > b * p * (q + 1)) → b ≤ 2) ∧
    (∀ c : ℝ, (∀ p q : ℤ, p^2 + q^2 + 1 > c * p * (q + 1)) → c ≤ 3) := by
  constructor 
  · -- (1) Prove: For any real numbers $p, q$, we have $p^{2}+q^{2}+1>p(q+1)$.
    intro p q 
    nlinarith [sq_nonneg (p - (q + 1) / 2), sq_nonneg (q - 1 / 2), sq_nonneg (p - 1 / 2), sq_nonneg (p - q), sq_nonneg (p - 1), sq_nonneg (q - 1 / 2), sq_nonneg (p - 1 / 2), sq_nonneg (q - 1 / 2)]
  constructor
  · -- (2) Find the largest real number $b$, such that for any real numbers $p, q$, we have $p^{2}+q^{2}+1>b p(q+1)$.
    intro b h
    have h1 := h 2 1
    norm_num at h1 
    nlinarith 
  · -- (3) Find the largest real number $c$, such that for any integers $p, q$, we have $p^{2}+q^{2}+1>c p(q+1)$.
    intro c h 
    have h3 := h 2 1 
    norm_num at h3 
    nlinarith