import Mathlib

theorem number_theory_241211 (a b c : ℤ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a^2 + b^2 = c^2) : 30 ∣ a * b * c := by
  have h2 : a * b * c % 2 = 0 := by
    by_contra h2
    push_neg at h2
    have ha1 : a % 2 = 1 := by
      by_contra h1
      push_neg at h1
      have h1' : a % 2 = 0 := by omega
      have h3 : (a * b * c) % 2 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have hb1 : b % 2 = 1 := by
      by_contra h1
      push_neg at h1
      have h1' : b % 2 = 0 := by omega
      have h3 : (a * b * c) % 2 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have hc1 : c % 2 = 1 := by
      by_contra h1
      push_neg at h1
      have h1' : c % 2 = 0 := by omega
      have h3 : (a * b * c) % 2 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have h4 : (a ^ 2) % 2 = 1 := by
      simp [ha1, pow_two, Int.add_emod, Int.mul_emod]
    have h5 : (b ^ 2) % 2 = 1 := by
      simp [hb1, pow_two, Int.add_emod, Int.mul_emod]
    have h6 : (c ^ 2) % 2 = 1 := by
      simp [hc1, pow_two, Int.add_emod, Int.mul_emod]
    have h7 : (a ^ 2 + b ^ 2) % 2 = (c ^ 2) % 2 := by
      omega
    omega
  have h3 : a * b * c % 3 = 0 := by
    by_contra h3
    push_neg at h3
    have ha1 : a % 3 = 1 ∨ a % 3 = 2 := by
      by_contra h1
      push_neg at h1
      have h1' : a % 3 = 0 := by omega
      have h3' : (a * b * c) % 3 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have hb1 : b % 3 = 1 ∨ b % 3 = 2 := by
      by_contra h1
      push_neg at h1
      have h1' : b % 3 = 0 := by omega
      have h3' : (a * b * c) % 3 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have hc1 : c % 3 = 1 ∨ c % 3 = 2 := by
      by_contra h1
      push_neg at h1
      have h1' : c % 3 = 0 := by omega
      have h3' : (a * b * c) % 3 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have h4 : (a ^ 2) % 3 = 1 := by
      rcases ha1 with (h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod]
    have h5 : (b ^ 2) % 3 = 1 := by
      rcases hb1 with (h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod]
    have h7 : (c ^ 2) % 3 = 1 := by
      rcases hc1 with (h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod]
    have h8 : (a ^ 2 + b ^ 2) % 3 = (c ^ 2) % 3 := by
      omega
    omega
  have h5 : a * b * c % 5 = 0 := by
    by_contra h5
    push_neg at h5
    have ha1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      by_contra h1
      push_neg at h1
      have h1' : a % 5 = 0 := by omega
      have h5' : (a * b * c) % 5 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have hb1 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
      by_contra h1
      push_neg at h1
      have h1' : b % 5 = 0 := by omega
      have h5' : (a * b * c) % 5 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have hc1 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by
      by_contra h1
      push_neg at h1
      have h1' : c % 5 = 0 := by omega
      have h5' : (a * b * c) % 5 = 0 := by
        simp [h1', Int.mul_emod]
      omega
    have h7 : (a ^ 2) % 5 = 1 ∨ (a ^ 2) % 5 = 4 := by
      rcases ha1 with (h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod]
    have h8 : (b ^ 2) % 5 = 1 ∨ (b ^ 2) % 5 = 4 := by
      rcases hb1 with (h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod]
    have h9 : (c ^ 2) % 5 = 1 ∨ (c ^ 2) % 5 = 4 := by
      rcases hc1 with (h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod]
    have h11 : (a ^ 2 + b ^ 2) % 5 = (c ^ 2) % 5 := by
      omega
    omega
  omega