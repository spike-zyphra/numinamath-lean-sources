import Mathlib

/- Observe the following equations: $a+b=1$, $a^2+b^2=3$, $a^3+b^3=4$, $a^4+b^4=7$, $a^5+b^5=11$, ..., then $a^{10}+b^{10}=$ ? -/
theorem algebra_541477 {a b : ℝ} (h₀ : a + b = 1) (h₁ : a ^ 2 + b ^ 2 = 3) (h₂ : a ^ 3 + b ^ 3 = 4)
    (h₃ : a ^ 4 + b ^ 4 = 7) (h₄ : a ^ 5 + b ^ 5 = 11) :
    a ^ 10 + b ^ 10 = 123 := by
  let f := fun n => a ^ n + b ^ n
  have hf n : f (n + 2) = f (n + 1) + f n := by
    have hprod : a * b = -1 := by
      calc a * b
        _ = ((a + b) ^ 2 - (a ^ 2 + b ^ 2)) / 2 := by ring
        _ = -1 := by norm_num [h₀, h₁]
    calc a ^ (n + 2) + b ^ (n + 2)
      _ = (a + b) * (a ^ (n + 1) + b ^ (n + 1)) - a * b * (a ^ n + b ^ n) := by ring
      _ = 1 * (a ^ (n + 1) + b ^ (n + 1)) - (-1) * (a ^ n + b ^ n) := by rw [h₀, hprod]
      _ = (a ^ (n + 1) + b ^ (n + 1)) + (a ^ n + b ^ n) := by ring
  change f 4 = 7 at h₃
  change f 5 = 11 at h₄
  have h₅ : f 6 = 18 := by
    norm_num [hf 4, h₃, h₄]
  have h₆ : f 7 = 29 := by
    norm_num [hf 5, h₄, h₅]
  have h₇ : f 8 = 47 := by
    norm_num [hf 6, h₅, h₆]
  have h₈ : f 9 = 76 := by
    norm_num [hf 7, h₆, h₇]
  have h₉ : f 10 = 123 := by
    norm_num [hf 8, h₇, h₈]
  exact h₉