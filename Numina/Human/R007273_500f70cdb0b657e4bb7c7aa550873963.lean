import Mathlib

/- Show that there are no integers $a,b,c$ for which $a^2+b^2-8c=6$. -/
theorem number_theory_51746 : ¬∃ a b c : ℤ, a^2 + b^2 - 8 * c = 6 := by 
  rintro ⟨a, b, c, hc⟩
  have := congr_arg (· % 8) hc
  simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, Int.emod_emod] at this
  have : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
    omega
  have : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
    omega
  have : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
    omega
  rcases this with (h | h | h | h | h | h | h | h) <;>
  rcases this with (h' | h' | h' | h' | h' | h' | h' | h') <;>
  rcases this with (h'' | h'' | h'' | h'' | h'' | h'' | h'' | h'') <;>
  simp [h, h', h''] at this <;>
  omega