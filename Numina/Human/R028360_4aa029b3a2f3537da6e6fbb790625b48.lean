import Mathlib

open Finset

/-
In the sequence $\left\{a_{n}\right\}$, $a_{1}=2, a_{n}+a_{n+1}=1\left(n \in \mathbf{N}_{+}\right)$,
let $S_{n}$ be the sum of the first $n$ terms of the sequence $a_{n}$,
then the value of $S_{2017}-$ $2 S_{2018}+S_{2019}$ is $3$.
-/
theorem algebra_184247 (a : ℕ → ℤ) (ha1 : a 1 = 2) (ha2 : ∀ n > 0, a n + a (n + 1) = 1) :
    let S n := ∑ i ∈ Icc 1 n, a i
    S 2017 - 2 * S 2018 + S 2019 = 3 := by
  intro S

-- First, we observe the recursive relation $a_{n+1} = 1 - a_n$.
-- This results in the sequence alternating between 2 and $-1$:
-- $a_1 = 2$, $a_2 = -1$, $a_3 = 2$, $a_4 = -1$, and so on.
  have h1 k (hk : k > 0) : a (2 * k - 1) = 2 ∧ a (2 * k) = -1 := by
    have c1 k (hk : k > 0) : 2 * k ≥ 1 := by omega
    have c2 k (hk : k > 0) : a (2 * k - 1) + a (2 * k) = 1 := by
      simpa [c1 k hk] using ha2 (2 * k - 1) (by omega)
    revert k
    apply Nat.le_induction
    . simp
      have c3 : a 2 = -1 := by
        specialize ha2 1 (by norm_num)
        ring_nf at ha2 ha1 ⊢
        omega
      simp [ha1, c3]
    . intro k hk ih
      have c3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      have c4 : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [c3, c4]
      have c5 : a (2 * k + 1) = 2 := by
        specialize ha2 (2 * k) (by omega)
        ring_nf at ih ha2 ⊢
        omega
      have c6 : a (2 * k + 2) = -1 := by
        specialize ha2 (2 * k + 1) (by omega)
        ring_nf at c5 ha2 ⊢
        omega
      simp [c5, c6]

-- For the sum $S_n$ of the first $n$ terms:
-- - If $n$ is even, $S_n = \frac{n}{2}$ because each pair of terms sums to 1.
  have h2 n (hn : n > 0) (hn2 : Even n) : S n = (n / 2 : ℚ) := by
    dsimp [S]
    obtain ⟨k, hk⟩ := hn2
    replace hk : n = 2 * k := by omega
    rw [hk]
    let t i : Finset ℕ := {2 * i - 1, 2 * i}
    let s := Icc 1 k
    have c1 : Icc 1 (2 * k) = s.biUnion t := by
      ext x
      constructor <;> intro d1
      . simp at d1
        simp only [mem_biUnion, s, t]
        use (x + 1) / 2
        simp
        omega
      . obtain ⟨y, hy1, hy2⟩ := by simpa [mem_biUnion, s, t] using d1
        simp
        omega
    have c2 : Set.PairwiseDisjoint s t := by
      intro i hi j hj hij a hai haj x hx
      specialize hai hx
      specialize haj hx
      simp [s] at hi hj
      simp [t] at hai haj
      omega
    rw [c1, sum_biUnion c2]
    have c3 : ∑ x ∈ s, ∑ i ∈ t x, a i = ∑ x ∈ Icc 1 k, 1 := by
      apply sum_congr rfl
      intro j hj
      simp [s] at hj
      rw [sum_pair]
      . specialize h1 j (by omega)
        omega
      . omega
    rw [c3]
    field_simp

-- - If $n$ is odd, $S_n = \frac{n + 3}{2}$ because there are $\frac{n-1}{2}$ pairs (each summing to 1) plus an additional 2.
  have h3 n (hn : n > 0) (hn2 : Odd n) : S n = ((n + 3) / 2 : ℚ) := by
    dsimp [S]
    obtain ⟨k, hk⟩ := hn2
    rw [hk]
    let t i : Finset ℕ := {2 * i, 2 * i + 1}
    let s := Icc 1 k
    have c1 : Icc 2 (2 * k + 1) = s.biUnion t := by
      ext x
      constructor <;> intro d1
      . simp at d1
        simp only [mem_biUnion, s, t]
        use x / 2
        simp
        omega
      . obtain ⟨y, hy1, hy2⟩ := by simpa [mem_biUnion, s, t] using d1
        simp
        omega
    have c2 : Set.PairwiseDisjoint s t := by
      intro i hi j hj hij a hai haj x hx
      specialize hai hx
      specialize haj hx
      simp [s] at hi hj
      simp [t] at hai haj
      omega
    rw [←sum_sdiff (show {1} ⊆ Icc 1 (2 * k + 1) from by intro x; simp; omega)]
    rw [show Icc 1 (2 * k + 1) \ {1} = Icc 2 (2 * k + 1) from by ext x; simp; omega]
    rw [c1, sum_biUnion c2]
    have c3 : ∑ x ∈ s, ∑ i ∈ t x, a i = ∑ x ∈ Icc 1 k, 1 := by
      apply sum_congr rfl
      intro j hj
      simp [s] at hj
      rw [sum_pair]
      . specialize ha2 (2 * j) (by omega)
        omega
      . omega
    rw [c3]
    field_simp [ha1]
    norm_cast
    omega

-- Given the specific values:
-- - $2017$ is odd, so $S_{2017} = \frac{2017 + 3}{2} = 1010$.
  have h4 : S 2017 = 1010 := by
    specialize h3 2017 (by norm_num) (by rw [Nat.odd_iff])
    qify
    norm_num [h3]
-- - $2018$ is even, so $S_{2018} = \frac{2018}{2} = 1009$.
  have h5 : S 2018 = 1009 := by
    specialize h2 2018 (by norm_num) (by rw [Nat.even_iff])
    qify
    norm_num [h2]
-- - $2019$ is odd, so $S_{2019} = \frac{2019 + 3}{2} = 1011$.
  have h6 : S 2019 = 1011 := by
    specialize h3 2019 (by norm_num) (by rw [Nat.odd_iff])
    qify
    norm_num [h3]

-- Substituting these into the expression $S_{2017} - 2S_{2018} + S_{2019}$:
-- $$1010 - 2 \times 1009 + 1011 = 1010 - 2018 + 1011 = (1010 + 1011) - 2018 = 2021 - 2018 = 3$$
-- Thus, the value of $S_{2017} - 2S_{2018} + S_{2019}$ is $\boxed{3}$.
  norm_num [h4, h5, h6]
