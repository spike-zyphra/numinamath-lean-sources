import Mathlib

theorem number_theory_113742 {a b : ℕ} (ha : a - 4 = 3 * ∑ i ∈ Finset.range 2014, 4 ^ (i + 1)) (hb : b - 8 = 5 * ∑ i ∈ Finset.range 2015, 6 ^ (i + 1)) :
    IsSquare a ∧ ¬IsSquare b := by
  have h1 : a = 4 ^ 2015 := by
    have eq1 : a - 4 = 3 * ∑ i in Finset.range 2014, 4 ^ (i + 1) := ha
    have h_sum1 : ∑ i in Finset.range 2014, 4 ^ (i + 1) = (4 ^ 2015 - 4) / 3 := by
      native_decide
    rw [h_sum1] at eq1
    have h3 : 3 * ((4 ^ 2015 - 4) / 3) = 4 ^ 2015 - 4 := by
      omega
    have eq2 : a - 4 = 4 ^ 2015 - 4 := by
      omega
    omega
  have h2 : b = 2 + 6 ^ 2016 := by
    have eq1 : b - 8 = 5 * ∑ i in Finset.range 2015, 6 ^ (i + 1) := hb
    have h_sum2 : ∑ i in Finset.range 2015, 6 ^ (i + 1) = (6 ^ 2016 - 6) / 5 := by
      native_decide
    rw [h_sum2] at eq1
    have h4 : 5 * ((6 ^ 2016 - 6) / 5) = 6 ^ 2016 - 6 := by
      have h2 : (6 ^ 2016 - 6) % 5 = 0 := by
        omega
      omega
    have eq2 : b - 8 = 6 ^ 2016 - 6 := by
      omega
    omega
  constructor
  · -- Show a is a perfect square
    rw [h1]
    exact ⟨2 ^ 2015, by norm_num⟩
  · -- Show b is not a perfect square
    rw [h2]
    intro h
    rcases h with ⟨k, hk⟩
    have h1 : k ^ 2 = 2 + 6 ^ 2016 := by
      nlinarith
    have h4 : k ^ 2 % 4 = 2 := by
      have h4_mod : (2 + 6 ^ 2016 : ℕ) % 4 = 2 := by
        omega
      omega
    have h3 : k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1 := by
      have h1 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.mul_mod, h1] at *
    omega