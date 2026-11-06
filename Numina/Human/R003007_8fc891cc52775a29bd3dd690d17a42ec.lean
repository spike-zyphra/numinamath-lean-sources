import Mathlib

/- 16. (2005 Belarusian Mathematical Olympiad) Let $a, b$ be positive integers such that $79 \mid(a+77 b)$, and $77 \mid(a+79 b)$, find the smallest possible value of the sum $a+b$. -/
theorem number_theory_142997 :
    IsLeast {x | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ 79 ∣ (a + 77 * b) ∧ 77 ∣ (a + 79 * b) ∧ x = a + b} 193 := by
  constructor
    -- 193 is in the set due to 155, 38 as witness for a, b
  . use 155, 38
    norm_num
    -- to prove 193 is a lower bound, first assume x is one number with a, b
  . rintro x ⟨a, b, ha, hb, h₁, h₂, hx⟩
    rw [hx]; clear hx
    -- 79 and 77 both divide 39 * a + b by linear manipulation
    replace h₁ : 79 ∣ 39 * a + b := by omega
    replace h₂ : 77 ∣ 39 * a + b := by omega
    -- as 79, 77 are coprime, their product also divide 39 * a + b
    have h_77_79 : IsCoprime (77:ℤ) 79 := by norm_num
    have : 77 * 79 ∣ 39 * a + b := by exact IsCoprime.mul_dvd h_77_79 h₂ h₁
    -- extracting the factor k from last statement, we see 39 ∣ k + b
    obtain ⟨k, hk⟩ := this
    have h₃ : 39 * (a + b) = (78^2 - 39) * k + 38 * (k + b) := by linarith
    have h₄ : 39 ∣ k + b := by omega
    -- k is positive from k's defining equation
    have hk' : 0 < k := by linarith
    -- there fore 39 ≤ k + b and then (78^2 - 39 + 38 * 39) ≤  39 * (a + b)
    replace h₄ : 39 ≤ k + b := by omega
    replace h₃ : (78^2 - 39 + 38 * 39) ≤  39 * (a + b) := by linarith
    -- then target is proved easily
    linarith