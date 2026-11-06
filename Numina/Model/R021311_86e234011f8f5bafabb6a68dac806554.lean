import Mathlib

theorem number_theory_176938 (f : ℝ → ℝ) (hf : f = fun x => (x^2 - x + 1) / 5) :
    ¬ ∃ x y : ℤ, f x = y := by
  rintro ⟨x, y, h⟩
  have h1 : (x : ℝ) ^ 2 - (x : ℝ) + 1 = 5 * (y : ℝ) := by
    rw [hf] at h
    simp at h
    nlinarith
  have h2 : x ^ 2 - x + 1 = 5 * y := by
    exact_mod_cast h1
  have h3 : (x ^ 2 - x + 1) % 5 = 0 := by
    omega
  have h4 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
    omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4)
  · -- x ≡ 0 (mod 5)
    simp [Int.add_emod, Int.mul_emod, h4, Int.sub_emod, pow_two] at h3
    all_goals omega
  · -- x ≡ 1 (mod 5)
    simp [Int.add_emod, Int.mul_emod, h4, Int.sub_emod, pow_two] at h3
    all_goals omega
  · -- x ≡ 2 (mod 5)
    simp [Int.add_emod, Int.mul_emod, h4, Int.sub_emod, pow_two] at h3
    all_goals omega
  · -- x ≡ 3 (mod 5)
    simp [Int.add_emod, Int.mul_emod, h4, Int.sub_emod, pow_two] at h3
    all_goals omega
  · -- x ≡ 4 (mod 5)
    simp [Int.add_emod, Int.mul_emod, h4, Int.sub_emod, pow_two] at h3
    all_goals omega