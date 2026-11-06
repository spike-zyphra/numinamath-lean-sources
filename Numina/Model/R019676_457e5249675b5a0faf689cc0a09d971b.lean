import Mathlib

theorem number_theory_5893
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hxy : ∃ x y, a * x + b * y = 1) :
    (∀ n, a ∣ n → b ∣ n → a * b ∣ n) ∧
    (∀ n, a ∣ b * n → a ∣ n) := by

  have h1 : IsCoprime a b := by
    rcases hxy with ⟨x, y, hxy⟩
    use x, y
    all_goals linarith

  constructor
  · -- Proof of (i): If $a \mid n$ and $b \mid n$, then $a * b \mid n$
    intro n ha1 hb1
    have h2 : IsCoprime a b := h1
    have h3 : a * b ∣ n := by
      apply IsCoprime.mul_dvd h2 ha1 hb1
    tauto
  · -- Proof of (ii): If $a \mid b * n$, then $a \mid n$
    intro n ha2
    have h1' : IsCoprime a b := h1
    have h3 : a ∣ n := by
      apply h1'.dvd_of_dvd_mul_left ha2
    tauto