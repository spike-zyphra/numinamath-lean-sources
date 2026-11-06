import Mathlib

open Nat

-- Let $r \ge 2$ be an integer. Let $n$ be a number in the decimal system whose representation consists of the $r$-fold repetition of a two-digit block $\overline{xy}$, i.e., $n = \overline{xyxy...xy}$ where $\overline{xy}$ is repeated $r$ times. Assume $x \neq 0$, so that $\overline{xy}$ is indeed a two-digit number ranging from $10$ to $99$. Let $P_r$ denote the largest prime factor of the number $S_r = \sum_{j=0}^{r-1} 100^j$. Show that the largest prime divisor of $n$ is $\max(P_r, 97)$.
theorem number_theory_636373 {r : ℕ} (hr : 2 ≤ r)
    {Pᵣ} (isGreatest_Pᵣ : IsGreatest (∑ j ∈ Finset.range r, 100 ^ j).primeFactors Pᵣ) :
    IsGreatest { p | ∃ x y, (x < 10 ∧ x ≠ 0) ∧ y < 10 ∧
      let n := ∑ i ∈ Finset.range r, 100 ^ i * (10 * x + y); p ∈ n.primeFactors
    } (max Pᵣ 97) := by
  have : { p | ∃ x y, (x < 10 ∧ x ≠ 0) ∧ y < 10 ∧
        let n := ∑ i ∈ Finset.range r, 100 ^ i * (10 * x + y); p ∈ n.primeFactors
      } = { p | ∃ xy, (xy ≥ 10 ∧ xy ≤ 99) ∧ p ∈ ((∑ j ∈ Finset.range r, 100 ^ j) * xy).primeFactors} := by
    ext p
    have sum_mul_xy xy : (∑ j ∈ Finset.range r, 100 ^ j) * xy = ∑ i ∈ Finset.range r, 100 ^ i * xy := by
      exact Finset.sum_mul (Finset.range r) (HPow.hPow 100) xy
    constructor
    . simp [-mem_primeFactors]
      intro x x_lt_10 x_ne_0 y y_lt_10 p_mem
      set xy := 10 * x + y
      use xy
      constructor
      . omega
      . convert p_mem
        . exact sum_mul_xy xy
    . simp [-mem_primeFactors]
      intro xy _10_le_xy xy_le_99 p_mem
      let x := xy / 10
      use x
      constructor
      . omega
      . let y := xy % 10
        use y
        constructor
        . omega
        . convert p_mem
          . have : 10 * x + y = xy := by
              omega
            rw [this]
            exact (sum_mul_xy xy).symm
  rw [this]
  have left_ne_0 : (∑ j ∈ Finset.range r, 100 ^ j) * 97 ≠ 0 := by
    /-
        have : Finset.range r = {0} ∪ Finset.Ico 1 r := by
          ext j
          simp
          omega
        rw [this]
        have : Disjoint {0} (Finset.Ico 1 r) := by
          simp
        rw [Finset.sum_union this]
        simp
         -/
        simp
        use 0
        linarith
  constructor
  . simp [-mem_primeFactors] -- maybe `simp` less and don't produce `∃ x, x < r`
    use 97
    simp [-mem_primeFactors]
    set primeFactors := ((∑ j ∈ Finset.range r, 100 ^ j) * 97).primeFactors
    have Pᵣ_mem_primeFactors : Pᵣ ∈ primeFactors := by
      unfold primeFactors
      have Pᵣ_mem_left_primeFactors : Pᵣ ∈ ((∑ j ∈ Finset.range r, 100 ^ j).primeFactors : Set ℕ) :=
        isGreatest_Pᵣ.1
      norm_cast at this
      have : ∑ j ∈ Finset.range r, 100 ^ j ∣ (∑ j ∈ Finset.range r, 100 ^ j) * 97 := by
        exact Nat.dvd_mul_right (∑ j ∈ Finset.range r, 100 ^ j) 97
      have left_primeFactors_subset : (∑ j ∈ Finset.range r, 100 ^ j).primeFactors ⊆ ((∑ j ∈ Finset.range r, 100 ^ j) * 97).primeFactors := by
        exact primeFactors_mono this left_ne_0
      exact left_primeFactors_subset Pᵣ_mem_left_primeFactors
    have _97_mem_primeFactors : 97 ∈ primeFactors := by
      simp [primeFactors]
      constructor
      . decide
      . use 0
        linarith
    --apply?
    by_cases w_Pᵣ_le_97 : Pᵣ ≤ 97
    . simp [w_Pᵣ_le_97]
      exact _97_mem_primeFactors
    . /-
      simp at w_Pᵣ_le_97
      simp [w_Pᵣ_le_97]
       -/
      have : 97 ≤ Pᵣ := by
        linarith
      simp [this]
      exact Pᵣ_mem_primeFactors
  . simp [upperBounds, -mem_primeFactors]
    intro p xy le_xy xy_le p_mem_primeFactors
    have left_primeFactor_le_Pᵣ := isGreatest_Pᵣ.2
    simp only [upperBounds] at left_primeFactor_le_Pᵣ
    have : ((∑ j ∈ Finset.range r, 100 ^ j) * xy).primeFactors =
        (∑ j ∈ Finset.range r, 100 ^ j).primeFactors ∪ xy.primeFactors := by
      refine primeFactors_mul ?_ ?_
      . omega
      . linarith
    simp only [this, Finset.mem_union] at p_mem_primeFactors
    rcases p_mem_primeFactors with p_mem_left | p_mem_right
    . left
      exact left_primeFactor_le_Pᵣ p_mem_left
    . right
      simp at p_mem_right
      rcases p_mem_right with ⟨p_prime, p_dvd_xy, _⟩
      have : p ≤ 99 := by
        have : p ≤ xy := by
          apply Nat.le_of_dvd
          . linarith
          . exact p_dvd_xy
        linarith
      by_contra p_gt_97
      simp at p_gt_97
      clear p_dvd_xy
      revert p_prime
      revert p
      decide
