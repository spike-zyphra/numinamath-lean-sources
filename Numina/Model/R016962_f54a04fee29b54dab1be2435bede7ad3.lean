import Mathlib

theorem number_theory_87903 (a b : ℤ) : 7 ∣ a^2 + b^2 + 1 → ¬ 7 ∣ a + b := by
  intro h
  by_contra h1

  have h2 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
    omega
  have h3 : b % 7 = (- (a % 7) ) % 7 := by
    omega
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2)
  · -- a ≡ 0
    have ha : a % 7 = 0 := by
      omega
    have hb : b % 7 = 0 := by
      simp [ha] at h3
      omega
    have h4 : (a ^ 2 + b ^ 2 + 1) % 7 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, Int.sub_emod]
      <;> omega
    omega
  · -- a ≡ 1
    have ha : a % 7 = 1 := by
      omega
    have hb : b % 7 = 6 := by
      simp [ha] at h3
      omega
    have h4 : (a ^ 2 + b ^ 2 + 1) % 7 = 3 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, Int.sub_emod]
      <;> omega
    omega
  · -- a ≡ 2
    have ha : a % 7 = 2 := by
      omega
    have hb : b % 7 = 5 := by
      simp [ha] at h3
      omega
    have h4 : (a ^ 2 + b ^ 2 + 1) % 7 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, Int.sub_emod]
      <;> omega
    omega
  · -- a ≡ 3
    have ha : a % 7 = 3 := by
      omega
    have hb : b % 7 = 4 := by
      simp [ha] at h3
      omega
    have h4 : (a ^ 2 + b^2 + 1) % 7 = 5 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, Int.sub_emod]
      <;> omega
    omega
  · -- a ≡ 4
    have ha : a % 7 = 4 := by
      omega
    have hb : b % 7 = 3 := by
      simp [ha] at h3
      omega
    have h4 : (a ^ 2 + b^2 + 1) % 7 = 5 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, Int.sub_emod]
      <;> omega
    omega
  · -- a ≡ 5
    have ha : a % 7 = 5 := by
      omega
    have hb : b % 7 = 2 := by
      simp [ha] at h3
      omega
    have h4 : (a ^ 2 + b^2 + 1) % 7 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, Int.sub_emod]
      <;> omega
    omega
  · -- a ≡ 6
    have ha : a % 7 = 6 := by
      omega
    have hb : b % 7 = 1 := by
      simp [ha] at h3
      omega
    have h4 : (a ^ 2 + b^2 + 1) % 7 = 3 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, ha, hb, Int.sub_emod]
      <;> omega
    omega