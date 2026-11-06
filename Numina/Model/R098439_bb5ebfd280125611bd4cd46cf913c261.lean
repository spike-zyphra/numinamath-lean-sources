import Mathlib

theorem algebra_98004 {z1 z2 : ℂ} (hz1 : z1^2 = 4 + 4 * Real.sqrt 15 * .I) (hz2 : z2^2 = 2 + 2 * Real.sqrt 3 * .I)
    (p q r s : ℕ) (hpqr : p > 0 ∧ q > 0 ∧ r > 0 ∧ s > 0)
    (hqr : ¬∃ p' : ℕ, p'^2 ∣ q) (hps : ¬∃ p' : ℕ, p'^2 ∣ s)
    (harea : (z2 - z1).im * (z2 - z1).re = p * Real.sqrt q - r * Real.sqrt s) :
    p + q + r + s = 20 := by
        have h1 : ∃ p' : ℕ, p' ^ 2 ∣ q := by
            use 1
            simp
        contradiction