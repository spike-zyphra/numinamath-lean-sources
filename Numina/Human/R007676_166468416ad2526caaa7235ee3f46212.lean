import Mathlib

/-
If $ a $ and $ b $ are integers both of the form $ 4n + 1 $, then the product $ ab $ is also of this form.
-/
theorem number_theory_4560
    (a b : ℤ)
    (h₀ : ∃ n, a = 4 * n + 1)
    (h₁ : ∃ n, b = 4 * n + 1) :
    ∃ n, a * b = 4 * n + 1 := by
  -- given a=4r+1
  obtain ⟨r, hr⟩ := h₀
  -- and b=4s+1
  obtain ⟨s, hs⟩ := h₁
  -- we can deduce that ab = 4(4rs+r+s)+1
  use (4 * r * s + r + s)
  rw [hr, hs]
  ring
