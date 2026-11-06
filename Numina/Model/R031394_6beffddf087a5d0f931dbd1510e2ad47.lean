import Mathlib

/- Prover que l'équation

$$
a^{3}+b^{5}+c^{7}+d^{11}=e^{13}
$$

admet une infinité de solutions en entiers strictement positifs. -/
theorem number_theory_607476 :
    Set.Infinite {(a, b, c, d, e) : ℤ × ℤ × ℤ × ℤ × ℤ |
      a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ a^3 + b^5 + c^7 + d^11 = e^13} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) =>
    (2^(385 * (13 * n + 1)), 2^(231 * (13 * n + 1)), 2^(165 * (13 * n + 1)), 2^(105 * (13 * n + 1)), 2^(1155 * n + 89)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h 
    all_goals 
      omega
  · -- Show that ∀ n, f n ∈ S
    intro n
    simp only [Set.mem_setOf_eq]
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    · -- Verify the equation
      -- The equation
      -- (2^(385 * (13 * n + 1)))^3 + (2^(231 * (13 * n + 1)))^5 + (2^(165 * (13 * n + 1)))^7 + (2^(105 * (13 * n + 1)))^11 = (2^(1155 * n + 89))^13
      have h1 : (2 : ℤ) ^ (385 * (13 * n + 1) * 3) = (2 : ℤ) ^ (1155 * (13 * n + 1)) := by
        ring_nf
      have h2 : (2 : ℤ) ^ (231 * (13 * n + 1) * 5) = (2 : ℤ) ^ (1155 * (13 * n + 1)) := by
        ring_nf
      have h3 : (2 : ℤ) ^ (165 * (13 * n + 1) * 7) = (2 : ℤ) ^ (1155 * (13 * n + 1)) := by
        ring_nf
      have h4 : (2 : ℤ) ^ (105 * (13 * n + 1) * 11) = (2 : ℤ) ^ (1155 * (13 * n + 1)) := by
        ring_nf
      calc
        (2^(385 * (13 * n + 1)) : ℤ) ^ 3 + (2^(231 * (13 * n + 1)) : ℤ) ^ 5 + (2^(165 * (13 * n + 1)) : ℤ) ^ 7 + (2^(105 * (13 * n + 1)) : ℤ) ^ 11
          = (2 : ℤ) ^ (385 * (13 * n + 1) * 3) + (2 : ℤ) ^ (231 * (13 * n + 1) * 5) + (2 : ℤ) ^ (165 * (13 * n + 1) * 7) + (2 : ℤ) ^ (105 * (13 * n + 1) * 11) := by
            ring_nf
        _ = (4 : ℤ) * (2 : ℤ) ^ (1155 * (13 * n + 1)) := by
            rw [h1, h2, h3, h4]
            all_goals ring_nf
        _ = (2 : ℤ) ^ (1155 * (13 * n + 1) + 2) := by
            ring_nf
        _ = (2 : ℤ) ^ ((1155 * n + 89) * 13) := by
            have h10 : 1155 * (13 * n + 1) + 2 = (1155 * n + 89) * 13 := by
              omega
            rw [h10]
        _ = ( (2 : ℤ) ^ (1155 * n + 89) ) ^ 13 := by
            rw [pow_mul]
        _ = ( (2^(1155 * n + 89) : ℤ) ) ^ 13 := by
            ring_nf