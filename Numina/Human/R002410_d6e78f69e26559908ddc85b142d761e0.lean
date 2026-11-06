import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

/- Let z = (1+i)/sqrt(2). What is
(z^(1^2) + z^(2^2) + z^(3^2) + ... + z^(12^2)) * (1/z^(1^2) + 1/z^(2^2) + 1/z^(3^2) + ... + 1/z^(12^2))
?
(A) 18
(B) 72−36*sqr(2)
(C) 36
(D) 72
(E) 72+36*sqrt(2)
-/
theorem algebra_92978 {z : ℂ} (hz : z = (1 + I) / Real.sqrt 2) :
(∑ i ∈ range 12, z ^ ((i + 1)^2)) * (∑ i ∈ range 12, 1 / z ^ ((i + 1)^2)) = 36 := by
  -- prove that z^2 = i, z^4 = -1, z^8 = 1, hence z^(a+8b) = z^a
  have hz_2 : z^2 = I := by
    calc
      z^2 = ((1+I)/√ 2)^2 := by rw [hz]
      _ = 1 / (√2)^2 + 2 * I / (√2)^2 + I ^ 2/(√2)^2 := by ring
      _ = 1 / 2 + 2 * I / 2 + -1 / 2 := by
        congr
        any_goals exact I_sq
        all_goals norm_cast
        all_goals refine Real.sq_sqrt ?_
        all_goals norm_num
      _ = I := by ring
  have hz_4 : z^4 = -1 := by
    calc
      z^4 = (z^2)^2 := by ring
      _ = -1 := by rw [hz_2]; simp
  have hz_8 : z^8 = 1 := by
    calc
      z^8 = (z^4)^2 := by ring
      _ = 1 := by rw [hz_4]; norm_cast
  have hz_mod (a b :ℕ) : z^(a + b * 8) = z^a := by
    calc
      z^(a+b*8) = z^a * (z^8)^b := by ring
      _ = z^a := by
        rw [hz_8]; simp
  -- use suitable a, b to map each of z^1^2, ... , z^12^2 to z^0, z^1, or z^4
  have h₁ : z^(1^2) = z := by simp
  have h₂ : z^(2^2) = z^4 := by simp [hz_4]
  have h₃ : z^(3^2) = z^1 := by rw [← hz_mod 1 1]; ring
  have h₄ : z^(4^2) = z^0 := by rw [← hz_mod 0 2]; ring
  have h₅ : z^(5^2) = z^1 := by rw [← hz_mod 1 3]; ring
  have h₆ : z^(6^2) = z^4 := by rw [← hz_mod 4 4]; ring
  have h₇ : z^(7^2) = z^1 := by rw [← hz_mod 1 6]; ring
  have h₈ : z^(8^2) = z^0 := by rw [← hz_mod 0 8]; ring
  have h₉ : z^(9^2) = z^1 := by rw [← hz_mod 1 10]; ring
  have h₁₀ : z^(10^2) = z^4 := by rw [← hz_mod 4 12]; ring
  have h₁₁ : z^(11^2) = z^1 := by rw [← hz_mod 1 15]; ring
  have h₁₂ : z^(12^2) = z^0 := by rw [← hz_mod 0 18]; ring
  -- so first sum reduces to 6z
  have hsum₁ : ∑ i ∈ range 12, z ^ ((i + 1)^2) = 6 * z := by
    calc
      ∑ i ∈ range 12, z ^ ((i + 1)^2) = z^1^2 + z^2^2 + z^3^2 + z^4^2 + z^5^2 + z^6^2 + z^7^2 + z^8^2 + z^9^2 + z^10^2 + z^11^2 + z^12^2 := by simp [sum_range_succ]
      _ = 6 * z := by
        rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, hz_4]
        norm_num
        ring
  -- second sum reduces to 6/z
  have hsum₂ :∑ i ∈ range 12, 1 / z ^ ((i + 1)^2) = 6 / z := by
    calc
      ∑ i ∈ range 12, 1 / z ^ ((i + 1)^2) = 1 / z^1^2 + 1 / z^2^2 + 1 / z^3^2 + 1 / z^4^2 + 1 / z^5^2 + 1 / z^6^2 + 1 / z^7^2 + 1 / z^8^2 + 1 / z^9^2 + 1 / z^10^2 + 1 / z^11^2 + 1 / z^12^2 := by simp [sum_range_succ]
      _ = 6 / z := by
        rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, hz_4]
        norm_num
        ring
  rw [hsum₁, hsum₂]
  -- establish z ≠ 0
  have hz_nonzero : z ≠ 0 := by
    rw [hz]
    apply (not_congr normSq_eq_zero).mp
    dsimp [normSq]
    simp
  -- so 6z * 6/z = 36
  field_simp
  ring