import Mathlib

theorem number_theory_308959 (a b : ℤ) (ha : ¬(3 ∣ a)) (hb : ¬(3 ∣ b))
    (h : ¬(3 ∣ a - b)) :
    9 ∣ a^3 + b^3 := by
  have ha1 : a % 3 = 1 ∨ a % 3 = 2 := by
    omega
  have hb1 : b % 3 = 1 ∨ b % 3 = 2 := by 
    omega
  have ha2 : a % 3 = 1 ∨ a % 3 = 2 := by
    omega
  have hb2 : b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  have h8 : (a^3 + b^3) % 9 = 0 := by
    rcases ha1 with (ha1 | ha1)
    · -- Assume $a \equiv 1 \pmod{3}$
      rcases hb1 with (hb1 | hb1)
      · -- Assume $b \equiv 1 \pmod{3}$
        exfalso
        have : (a - b) % 3 = 0 := by
          omega
        omega
      · -- Assume $b \equiv 2 \pmod{3}$
        have ha1' : a % 9 = 1 ∨ a % 9 = 4 ∨ a % 9 = 7 := by
          omega
        have hb1' : b % 9 = 2 ∨ b % 9 = 5 ∨ b % 9 = 8 := by
          omega
        rcases ha1' with (ha1' | ha1' | ha1') <;> rcases hb1' with (hb1' | hb1' | hb1') <;> 
          simp [ha1', hb1', pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · -- Assume $a \equiv 2 \pmod{3}$
      rcases hb1 with (hb1 | hb1)
      · -- Assume $b \equiv 1 \pmod{3}$
        have ha1' : a % 9 = 2 ∨ a % 9 = 5 ∨ a % 9 = 8 := by
          omega
        have hb1' : b % 9 = 1 ∨ b % 9 = 4 ∨ b % 9 = 7 := by
          omega
        rcases ha1' with (ha1' | ha1' | ha1') <;> rcases hb1' with (hb1' | hb1' | hb1') <;> 
          simp [ha1', hb1', pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      · -- Assume $b \equiv 2 \pmod{3}$
        exfalso
        have : (a - b) % 3 = 0 := by
          omega
        omega
  exact Int.dvd_of_emod_eq_zero h8