import Mathlib

theorem number_theory_250249 (n : ℤ) :
    5 ∣ ∑ i ∈ Finset.range 5, (n + i)^2 ∧ ¬25 ∣ ∑ i ∈ Finset.range 5, (n + i)^2 := by
  have h1 : ∑ i in Finset.range 5, (n + i)^2 = 5 * (n^2 + 4 * n + 6) := by 
    simp [Finset.sum_range_succ]
    ring
  rw [h1] 
  constructor
  · -- Show that 5 divides the sum
    use n ^ 2 + 4 * n + 6
    all_goals ring
  · -- Show that 25 does not divide the sum
    intro h 
    have h3 : (n^2 + 4 * n + 6) % 5 ≠ 0 := by 
      have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
        omega
      rcases h4 with (h | h | h | h | h)
      · -- case n ≡ 0
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      · -- case n ≡ 1
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      · -- case n ≡ 2
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      · -- case n ≡ 3
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      · -- case n ≡ 4
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    omega