import Mathlib

/- Let $a, b, c$ be real numbers. Prove that

$$
a b+b c+c a+\max \{|a-b|,|b-c|,|c-a|\} \leq 1+\frac{1}{3}(a+b+c)^{2} .
$$ -/
theorem inequalities_604347 (a b c : ℝ) :
    a * b + b * c + c * a + max (max (|a - b|) (|b - c|)) (|c - a|) ≤
    1 + (1 / 3) * (a + b + c) ^ 2 := by

    -- with out loss of generality we can assume a ≤ b ≤ c
    wlog h : a ≤ b ∧ b ≤ c
    · -- reduce other cases to a ≤ b ≤ c
      by_cases hab : a ≤ b
      · -- a ≤ b
        by_cases hbc : b ≤ c
        · simp_all
        · have hcb : c ≤ b := by exact le_of_not_ge hbc
          by_cases hac : a ≤ c
          · -- a ≤ c ≤ b
            have res := this a c b ⟨hac, hcb⟩
            nth_rw 1 [max_comm] at res
            nth_rw 2 [max_comm] at res
            rw [← max_assoc, abs_sub_comm] at res
            nth_rw 2 [abs_sub_comm] at res
            nth_rw 3 [abs_sub_comm] at res
            linarith
          · -- c ≤ a ≤ b
            have hca : c ≤ a := by exact le_of_not_ge hac
            have res := this c a b ⟨hca, hab⟩
            rw [max_assoc, max_comm] at res
            linarith
      · -- b ≤ a
        have hba : b ≤ a := by exact le_of_not_ge hab
        by_cases hac : a ≤ c
        · -- b ≤ a ≤ c
          have res := this b a c ⟨hba, hac⟩
          rw [max_assoc] at res
          nth_rw 2 [max_comm] at res
          rw [← max_assoc] at res
          nth_rw 1 [abs_sub_comm] at res
          nth_rw 2 [abs_sub_comm] at res
          nth_rw 3 [abs_sub_comm] at res
          linarith
        · by_cases hcb : c ≤ b
          · -- c ≤ b ≤ a
            have res := this c b a ⟨hcb, hba⟩
            nth_rw 2 [max_comm] at res
            nth_rw 1 [abs_sub_comm] at res
            nth_rw 2 [abs_sub_comm] at res
            nth_rw 3 [abs_sub_comm] at res
            linarith
          · -- b ≤ c ≤ a
            have hbc : b ≤ c := by exact le_of_not_ge hcb
            have hca : c ≤ a := by exact le_of_not_ge hac
            have res := this b c a ⟨hbc, hca⟩
            rw [max_comm, ← max_assoc] at res
            linarith

    -- now that a ≤ b ≤ c, we show that max (max |a - b| |b - c|) |c - a| = c - a
    have hca_ab : |c - a| ≥ |b - a| := by apply abs_le_abs_of_nonneg <;> linarith
    nth_rw 2 [abs_sub_comm] at hca_ab

    have hca_bc : |c - a| ≥ |c - b| := by apply abs_le_abs_of_nonneg <;> linarith
    nth_rw 2 [abs_sub_comm] at hca_bc

    have hca_max : |c - a| ≥ max |a - b| |b - c| := max_le hca_ab hca_bc

    have hmax : max (max |a - b| |b - c|) |c - a| = |c - a| := max_eq_right hca_max
    rw [hmax]

    have habs : |c - a| = c - a := by apply abs_eq_self.mpr; linarith
    rw [habs]

    -- Now the goal changes to a * b + b * c + c * a + (c - a) ≤ 1 + 1 / 3 * (a + b + c) ^ 2
    -- we move all terms other than c - a to the right hand side
    suffices h : c - a ≤ 1 + 1 / 3 * (a + b + c) ^ 2 - a * b - b * c - c * a by linarith

    -- RHS can be reformed as 1 + 1 / 3 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a)
    have : 1 + 1 / 3 * (a + b + c) ^ 2 - a * b - b * c - c * a = 1 + 1 / 3 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by ring
    rw [this]

    -- and then as 1 + 1 / 6 * ((a - c) ^ 2 + (b - c) ^ 2 + (a - b) ^ 2)
    have : 1 + 1 / 3 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) = 1 + 1 / 6 * ((a - c) ^ 2 + (b - c) ^ 2 + (a - b) ^ 2) := by ring
    rw [this]

    -- here we prove a 2-variable version of HM-GM inequality
    have hm_am (x y : ℝ) : x ^ 2 + y ^ 2 ≥ 1 / 2 * (x + y) ^ 2 := by
      rw [add_sq]
      suffices h : x ^ 2 - 2 * x * y + y ^ 2 ≥ 0 by linarith
      rw [← sub_sq]
      apply sq_nonneg

    -- apply the HM-GM inequality, we show (b - c) ^ 2 + (a - b) ^ 2 ≥ 1 / 2 * (a - c) ^ 2
    have : (b - c) ^ 2 + (a - b) ^ 2 ≥ 1 / 2 * (a - c) ^ 2 := by
      linarith [hm_am (b - c) (a - b)]

    -- substituting this to RHS, we show that RHS ≥ 1 / 4 * (a - c) ^ 2
    have : 1 / 6 * ((a - c) ^ 2 + (b - c) ^ 2 + (a - b) ^ 2) ≥ 1 / 4 * (a - c) ^ 2 := by linarith

    -- now we only need to show 1 / 4 * (a - c) ^ 2 ≥ c - a,
    -- by simply reform it as a square.
    have : 1 + 1 / 4 * (a - c) ^ 2 ≥ c - a := by
      have : (a - c) ^ 2 = (c - a) ^ 2 := by ring
      rw [this]
      suffices h : (c - a) ^ 2 - 4 * (c - a) + 4 ≥ 0 by linarith
      have : (c - a) ^ 2 - 4 * (c - a) + 4 = ((c - a) - 2) ^ 2 := by ring
      rw [this]
      apply sq_nonneg

    linarith
