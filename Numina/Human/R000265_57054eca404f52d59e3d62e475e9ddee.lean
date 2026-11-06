import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all positive integers x such that 2x+1 is a perfect square
but none of the integers 2x+2, 2x+3, ..., 3x+2 are perfect squares. -/
theorem number_theory_8749 :
  {x : ℕ | 0 < x ∧ ∃ n , (2 * x + 1) = n^2 ∧ ∀ y ∈ Finset.Icc (2 * x + 2) (3 * x + 2), ¬ ∃ z, z^2 = y} = {4} := by
  -- prove by extensionality
  ext x
  simp
  constructor
  -- prove the latter contains the former
  · rintro ⟨hp, ⟨n, hn⟩, hrnsq⟩
    zify at hn
    -- prove n^2 - 1 is even
    have h' : (n:ℤ)^2 - 1 = 2*x := by {rw [← hn]; simp}
    have hnsq : 2 ∣ (n: ℤ)^2 - 1 := by exact Dvd.intro (↑x) (Eq.symm h')
    norm_cast at hn
    -- prove an inequality for later substitution
    have hnpl : 2 * x + 1 + 1 ≤ (n + 1) ^ 2 := by {rw [hn]; ring_nf; simp}
    -- solve x in terms of n
    rify at hn
    have hx : (x: ℝ) = (n^2 - 1)/2 := by {rw [← hn]; simp}
    -- find an inequality about n and x
    have hnp1 : (n + 1) ^ 2 > 3*x + 2 := by {
      by_contra hnh
      simp at hnh
      specialize hrnsq ((n+1)^2) hnpl hnh
      exact hrnsq (n + 1) rfl
    }
    -- substitute x in terms of n to get a inequality
    rify at hnp1
    rw [hx] at hnp1
    ring_nf at hnp1
    -- solve the quadratic inequality
    have qeq : ((n:ℝ)-2)^2 < 5 := by linarith
    have sqrtqeq : (n:ℝ) < 2+√5 := by linarith [lt_sqrt_of_sq_lt qeq]
    -- find an integer upper bound for n
    have sr5lsr9 : √5*√5 < 9 := by {simp; norm_num}
    have sr5l3 : √5 < 3 := by {nlinarith}
    have hrangen : (n:ℝ) < 5 := calc
      (n:ℝ) < 2+√5 := by exact sqrtqeq
          _ < 5 := by linarith
    norm_cast at hrangen
    clear sqrtqeq qeq hnp1 sr5lsr9 sr5l3 hnpl hn
    rify at hrnsq

    -- conduct a case-by-case analysis
    interval_cases n
    -- use assumption that n^-1 is even to find some contradictions in some cases
    all_goals norm_num at hx
    all_goals norm_num at hnsq
    -- case: x = 0
    · simp at *
      rify at hp
      rw [hx] at hp
      norm_num at hp
    -- case: x = 4
    · norm_cast at hx

  -- prove the former contains the latter
  · rintro hxeq4
    rw [hxeq4]
    simp
    constructor
    use 3
    norm_num
    intro y hly hry x hx
    -- find a contradiction
    have hxl : 3 < x := by nlinarith
    have hxr : x < 4 := by nlinarith
    linarith
