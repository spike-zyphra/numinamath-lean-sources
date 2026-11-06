import Mathlib


lemma lemma_1 (x d : ℤ) :
    x^3 + (x + d)^3 + (x + 2 * d)^3 = (x + 3 * d)^3 ↔
    x^3 - 6 * x * d^2 - 9 * d^3 = 0 := by
  constructor
  ·
    intro h
    ring_nf at h ⊢
    nlinarith
  ·
    intro h
    ring_nf at h ⊢
    nlinarith


lemma lemma_2 {x d : ℤ} (h : x^3 - 6*x*d^2 - 9*d^3 = 0) : x^3 + (x + d)^3 + (x + 2*d)^3 = (x + 3*d)^3 := by
  ring_nf
  nlinarith


theorem number_theory_271546 (x y z u : ℤ) (h : ∃ d, y = x + d ∧ z = y + d ∧ u = z + d)
    (h' : x^3 + y^3 + z^3 = u^3) :
    x % 3 = 0 ∧ y % 4 = 0 ∧ z % 5 = 0 ∧ u % 6 = 0 := by
  obtain ⟨d, hy, hz, hu⟩ := h
  have hz2 : z = x + 2 * d := by 
    linarith [hy, hz]
  have hu2 : u = x + 3 * d := by
    linarith [hz2, hu]
  rw [show y = x + d by linarith, show z = x + 2 * d by linarith, show u = x + 3 * d by linarith] at h'
  have eq1 : x^3 - 6 * x * d^2 - 9 * d^3 = 0 := by
    nlinarith [sq_nonneg (d), sq_nonneg (x^2 - 3 * x * d), sq_nonneg (d^2), sq_nonneg (x * d)]
  have h2 : (x - 3 * d) * (x^2 + 3 * d * x + 3 * d^2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Assume that $x - 3d = 0$, hence $x = 3d$.
    have hx1 : x = 3 * d := by linarith
    have hy1 : y = 4 * d := by
      linarith [hx1, hy]
    have hz1 : z = 5 * d := by
      linarith [hy1, hz2]
    have hu1 : u = 6 * d := by
      linarith [hz1, hu2]
    constructor
    · -- x ≡ 0 (mod 3)
      omega
    constructor
    · -- y ≡ 0 (mod 4)
      omega
    constructor
    · -- z ≡ 0 (mod 5)
      omega
    · -- u ≡ 0 (mod 6)
      omega
  · -- Assume that $x^2 + 3d x + 3d^2 = 0$.
    have eq2 : x^2 + 3 * d * x + 3 * d^2 = 0 := by
      nlinarith
    have h21 : (2 * x + 3 * d) ^ 2 + 3 * d ^ 2 = 0 := by
      nlinarith
    have h22 : d = 0 := by
      nlinarith [sq_nonneg (2 * x + 3 * d), sq_nonneg (d)]
    have h23 : x = 0 := by
      nlinarith [sq_nonneg (2 * x + 3 * d), sq_nonneg (d)]
    have hy1 : y = 0 := by
      nlinarith [hy, h23, h22]
    have hz1 : z = 0 := by
      nlinarith [hz2, h23, h22]
    have hu1 : u = 0 := by
      nlinarith [hu2, h23, h22]
    constructor
    · -- x ≡ 0 (mod 3)
      omega
    constructor
    · -- y ≡ 0 (mod 4)
      omega
    constructor
    · -- z ≡ 0 (mod 5)
      omega
    · -- u ≡ 0 (mod 6)
      omega