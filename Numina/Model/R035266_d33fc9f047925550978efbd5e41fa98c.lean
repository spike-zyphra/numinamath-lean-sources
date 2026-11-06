import Mathlib

lemma lemma_1
    (a b c k : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hk : k > a ∧ k > b ∧ k > c) :
    k^2 - k * (a + b + c) + a * b + b * c + c * a > 0 := by
  rcases hk with ⟨h1, h2, h3⟩
  have h4 : 0 < a * b := mul_pos ha hb
  have h5 : 0 < b * c := mul_pos hb hc
  have h6 : 0 < c * a := mul_pos hc ha
  have h7 : 0 < k - a := by linarith
  have h8 : 0 < k - b := by linarith
  have h9 : 0 < k - c := by linarith
  have h10 : 0 < (k - a) * (k - b) := mul_pos h7 h8
  have h11 : 0 < (k - b) * (k - c) := mul_pos h8 h9
  have h12 : 0 < (k - c) * (k - a) := mul_pos h9 h7
  nlinarith [sq_nonneg (k - a - b), sq_nonneg (k - b - c), sq_nonneg (k - c - a), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]


theorem inequalities_326965 (a b c x y z k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : a + x = k ∧ b + y = k ∧ c + z = k) :
    a * z + b * x + c * y < k ^ 2 := by
  rcases h with ⟨h1, h2, h3⟩
  have hx_eq : x = k - a := by linarith
  have hy_eq : y = k - b := by linarith
  have hz_eq : z = k - c := by linarith
  have hk1 : k > a := by linarith [show x > 0 from hx, hx_eq]
  have hk2 : k > b := by linarith [show y > 0 from hy, hy_eq]
  have hk3 : k > c := by linarith [show z > 0 from hz, hz_eq]
  have hquad_pos : k^2 - k * (a + b + c) + a * b + b * c + c * a > 0 := by
    apply lemma_1 a b c k ha hb hc ⟨hk1, hk2, hk3⟩
  have hx_sub : a * z + b * x + c * y = k * (a + b + c) - (a * b + b * c + c * a) := by
    rw [show z = k - c by linarith, show x = k - a by linarith, show y = k - b by linarith]
    nlinarith
  linarith