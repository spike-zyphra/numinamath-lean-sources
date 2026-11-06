import Mathlib

theorem number_theory_130765 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ Nat.gcd a b = 2 ∧ Nat.lcm a b = 60}.ncard = 4 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ Nat.gcd a b = 2 ∧ Nat.lcm a b = 60} = {(2, 60), (4, 30), (6, 20), (10, 12)} := by
    ext ⟨a, b⟩
    simp [-one_div]
    constructor
    · -- Assume ⟨a, b⟩ satisfies the constraints.
      rintro ⟨ha, hb, hab, hgcd, hlcm⟩
      have h2 : a ∣ 60 := by
        rw [← hlcm]
        apply Nat.dvd_lcm_left
      have h3 : b ∣ 60 := by
        rw [← hlcm]
        apply Nat.dvd_lcm_right
      have h4 : a ≤ 60 := by
        exact Nat.le_of_dvd (by norm_num) h2
      have h5 : b ≤ 60 := by
        exact Nat.le_of_dvd (by norm_num) h3
      interval_cases a <;> interval_cases b <;> norm_num [Nat.gcd, Nat.lcm] at *
      <;> tauto
    · -- Show that these four pairs indeed satisfy all constraints.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (2, 60)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd, Nat.lcm]
      · -- (4, 30)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd, Nat.lcm]
      · -- (6, 20)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd, Nat.lcm]
      · -- (10, 12)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.gcd, Nat.lcm]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }