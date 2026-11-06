import Mathlib

theorem number_theory_240187 (a b c d e f g h i : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hg' : h ≠ 0)
    (hg'' : i ≠ 0) (h1 : ∃ p q, p.Prime ∧ q.Prime ∧ p^2 + q^2 = a)
    (h2 : ∃ p q, p.Prime ∧ q.Prime ∧ q = p + 4 ∧ a * b = p * q)
    (h3 : ∃ p q, p.Prime ∧ q.Prime ∧ q = p + 4 ∧ a * b * c = 60 / 100 * (a + b + c)) :
    b = 397 := by
  rcases h1 with ⟨p, q, hp1, hq1, h1⟩
  rcases h2 with ⟨p2, q2, hp2, hq2, h2, h2'⟩
  rcases h3 with ⟨p3, q3, hp3, hq3, h3, h3'⟩
  norm_num at h3'
  all_goals
  have h9 : a * b * c = 0 := by
    omega
  have h5 : a * b * c ≠ 0 := by
    apply Nat.mul_ne_zero
    apply Nat.mul_ne_zero
    exact ha
    exact hb
    exact hc
  have h6 : b = 397 := by
    exfalso
    apply h5
    omega
  exact h6