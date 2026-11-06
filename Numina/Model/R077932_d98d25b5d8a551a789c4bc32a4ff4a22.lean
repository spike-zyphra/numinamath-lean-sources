import Mathlib

theorem number_theory_82380 (a b c d : ℤ) (h : 7 * a + 8 * b = 14 * c + 28 * d) :
    14 ∣ a * b := by
  have h1 : a % 2 = 0 := by
    have eq1 : 7 * a + 8 * b = 14 * c + 28 * d := by
      omega
    omega
  have h2 : b % 7 = 0 := by
    have eq1 : 7 * a + 8 * b = 14 * c + 28 * d := by
      omega
    omega
  have ha : 2 ∣ a := by 
    exact Int.dvd_of_emod_eq_zero h1
  have hb : 7 ∣ b := by 
    exact Int.dvd_of_emod_eq_zero h2
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  rw [hm, hn]
  -- Now we need to prove 14 divides (2 * m) * (7 * n)
  -- which is clear since it is equal to 14 * (m * n)
  use m * n
  ring