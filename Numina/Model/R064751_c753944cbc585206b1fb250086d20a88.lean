import Mathlib

theorem algebra_4782 (milk soda juice : ℕ) (h₀ : 5 * milk + 3 * soda + 6 * juice = 163)
    (h₁ : milk = soda + 3) (h₂ : juice = 2 * milk + 3) :
    soda = 8 := by
  rw [h₁] at h₀
  rw [show juice = 2 * (soda + 3) + 3 by 
    rw [h₂, h₁]
  ] at h₀ 
  omega