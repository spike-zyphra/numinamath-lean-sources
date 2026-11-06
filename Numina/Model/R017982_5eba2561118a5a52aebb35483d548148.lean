import Mathlib

theorem algebra_145870 {p q r k : Polynomial ℝ} (hq : q = 3 * X - 5) (hk : k = X ^ 2 - 2 * X + 7)
    (hr : r = 2) (hp : p / q = k ∧ p % q = r) :
    p = 3 * X ^ 3 - 11 * X ^ 2 + 31 * X - 33 := by
  have h1 : p = q * k + r := by
    rw [← EuclideanDomain.div_add_mod p q]
    have hdiv : p / q = k := hp.1
    have hmod : p % q = r := hp.2
    rw [hdiv, hmod]
    <;> ring_nf <;> norm_num
  rw [h1]
  rw [hq, hk, hr]
  ring_nf
  <;> norm_num
  <;> ring_nf