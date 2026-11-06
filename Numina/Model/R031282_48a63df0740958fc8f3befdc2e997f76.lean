import Mathlib





lemma lemma_1 {a b c : ℤ} (h : a^2 = c^2 + 4 * b) :
    2 * (a^2 - 2 * b) = a^2 + c^2 := by
  linarith


theorem algebra_114857 {a b c : ℤ} (h : a^2 = c^2 + 4 * b) :
    ∃ x y, a^2 - 2 * b = x^2 + y^2 := by
  have h1 : (a : ℤ) % 2 = (c : ℤ) % 2 := by
    have h2 : (a ^ 2 : ℤ) % 2 = (c ^ 2 : ℤ) % 2 := by
      have h3 : a ^ 2 = c ^ 2 + 4 * b := h
      have h4 : (a ^ 2 : ℤ) % 2 = (c ^ 2 + 4 * b : ℤ) % 2 := by rw [h3]
      simp at h4 ⊢
      omega
    have h3 : (a : ℤ) % 2 = 0 ∨ (a : ℤ) % 2 = 1 := by omega
    have h4 : (c : ℤ) % 2 = 0 ∨ (c : ℤ) % 2 = 1 := by omega
    rcases h3 with (h3 | h3)
    · -- If a % 2 = 0, then a ^ 2 % 2 = 0
      have h5 : (a ^ 2 : ℤ) % 2 = 0 := by
        simp [pow_two, Int.mul_emod, h3]
      rcases h4 with (h4 | h4)
      · -- If c % 2 = 0, then c ^ 2 % 2 = 0
        have h6 : (c ^ 2 : ℤ) % 2 = 0 := by
          simp [pow_two, Int.mul_emod, h4]
        omega
      · -- If c % 2 = 1, then c ^ 2 % 2 = 1
        have h6 : (c ^ 2 : ℤ) % 2 = 1 := by
          simp [pow_two, Int.mul_emod, h4]
        omega
    · -- If a % 2 = 1, then a ^ 2 % 2 = 1
      have h5 : (a ^ 2 : ℤ) % 2 = 1 := by
        simp [pow_two, Int.mul_emod, h3]
      rcases h4 with (h4 | h4)
      · -- If c % 2 = 0, then c ^ 2 % 2 = 0
        have h6 : (c ^ 2 : ℤ) % 2 = 0 := by
          simp [pow_two, Int.mul_emod, h4]
        omega
      · -- If c % 2 = 1, then c ^ 2 % 2 = 1
        have h6 : (c ^ 2 : ℤ) % 2 = 1 := by
          simp [pow_two, Int.mul_emod, h4]
        omega
  have h2 : ((a + c) : ℤ) % 2 = 0 := by
    omega
  have h3 : ((a - c) : ℤ) % 2 = 0 := by
    omega
  have h4 : ∃ k : ℤ, a + c = 2 * k := by
    refine' ⟨(a + c) / 2, by omega⟩
  rcases h4 with ⟨k, hk⟩
  have h5 : ∃ m : ℤ, a - c = 2 * m := by
    refine' ⟨(a - c) / 2, by omega⟩
  rcases h5 with ⟨m, hm⟩
  use k, m
  have h6 : a ^ 2 - 2 * b = k ^ 2 + m ^ 2 := by
    have h7 : a ^ 2 - 2 * b = (c ^ 2 + 4 * b) - 2 * b := by
      rw [show a ^ 2 = c ^ 2 + 4 * b by linarith]
    have h8 : (c ^ 2 + 4 * b) - 2 * b = c ^ 2 + 2 * b := by
      omega
    have h9 : c ^ 2 + 2 * b = k ^ 2 + m ^ 2 := by
      have h10 : k = (a + c) / 2 := by
        omega
      have h11 : m = (a - c) / 2 := by
        omega
      rw [h10, h11]
      have h15 : ((a + c) : ℤ) % 2 = 0 := h2
      have h16 : ((a - c) : ℤ) % 2 = 0 := h3
      have h13 : ∃ n, (a + c) = 2 * n := by
        refine' ⟨(a + c) / 2, by omega⟩
      rcases h13 with ⟨n, hn⟩
      have h14 : ∃ p, (a - c) = 2 * p := by
        refine' ⟨(a - c) / 2, by omega⟩
      rcases h14 with ⟨p, hp⟩
      have e1 : (a + c : ℤ) = 2 * n := by
        linarith
      have e2 : (a - c : ℤ) = 2 * p := by
        linarith
      have e3 : (a + c : ℤ) * (a - c : ℤ) = (4 * b : ℤ) := by
        have h67 : a ^ 2 - c ^ 2 = 4 * b := by 
          nlinarith
        have h68 : (a + c) * (a - c) = a ^ 2 - c ^ 2 := by
          ring
        rw [h68] at *
        linarith
      rw [e1, e2] at e3
      have e4 : (4 * (n * p : ℤ) : ℤ) = (4 * b : ℤ) := by
        nlinarith
      have e5 : (n * p : ℤ) = (b : ℤ) := by
        omega
      have eq1 : ((a + c) / 2 : ℤ) ^ 2 + ((a - c) / 2 : ℤ) ^ 2 = (n ^ 2 + p ^ 2 : ℤ) := by
        rw [show (a + c) / 2 = n by omega]
        rw [show (a - c) / 2 = p by omega]
      have eq7 : (c ^ 2 + 2 * b : ℤ) = (n ^ 2 + p ^ 2 : ℤ) := by
        rw [show c = n - p by omega]
        rw [show b = n * p by omega]
        nlinarith
      nlinarith
      all_goals
        nlinarith
    nlinarith
  linarith