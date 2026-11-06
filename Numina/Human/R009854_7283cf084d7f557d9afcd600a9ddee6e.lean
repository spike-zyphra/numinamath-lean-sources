import Mathlib

open Finset

/-- $1990-1980+1970-1960+\cdots -20+10 =$

$\text{(A)}\ -990 \qquad \text{(B)}\ -10 \qquad \text{(C)}\ 990 \qquad \text{(D)}\ 1000
\qquad \text{(E)}\ 1990$ -/
theorem algebra_97307 {a : ℕ → ℤ}
    (ha : ∀ i, a i = (-1 : ℤ)^i * (1990 - 10 * i)) : ∑ i ∈ range 200, a i = 1000 := by

  -- Let $a_i = (-1)^i \cdot (1990 - 10i)$. We want to find $\sum_{i=0}^{199} a_i$.

  -- For simplicity, let $b_i = a_{2i} + a_{2i + 1}$.
  let b i := a (2 * i) + a (2 * i + 1)

  -- We will show that $\sum_{i=0}^{199} a_i = \sum_{i=0}^{99} b_i$

  -- First of all, observe that $\sum_{i=0}^{99} a_i =
  -- $\sum_{i=0, i even}^{199} a_i + \sum_{i=0, i odd}^{199} a_i$.
  have h1 : ∑ i ∈ range 200, a i =
      ∑ i ∈ image (fun i ↦ 2 * i) (range 100), a i + ∑ i ∈ image (fun i ↦ 2 * i + 1) (range 100), a i := by
    -- This hold because the set {0, 1, \dots, 199} is the union of the sets {0, 2, \dots, 198} and
    -- {1, 3, \dots, 199} which are disjoint.
    rw [←Finset.sum_union]
    · apply Finset.sum_congr
      · ext i
        constructor
        · simp_intro hi
          by_cases hi' : Even i
          · left
            rcases hi' with ⟨a, ha⟩
            use a
            omega
          · right
            simp at hi'
            rcases hi' with ⟨a, ha⟩
            use a
            omega
        · simp_intro hi
          rcases hi with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> omega
      · simp_intro
    · rw [Finset.disjoint_iff_ne]
      simp
      intro i hi j hj h
      omega

  -- Moreover, $\sum_{i=0, i even}^{199} a_i = \sum_{i=0}^{99} a_{2i}$.
  have h2 : ∑ i ∈ range 100, a (2 * i) = ∑ i ∈ image (fun i ↦ 2 * i) (range 100), a i := by
    rw [Finset.sum_image]
    intro i hi j hj h
    omega

  -- Moreover, $\sum_{i=0, i odd}^{199} a_i = \sum_{i=0}^{99} a_{2i + 1}$.
  have h3 : ∑ i ∈ range 100, a (2 * i + 1) = ∑ i ∈ image (fun i ↦ 2 * i + 1) (range 100), a i := by
    rw [Finset.sum_image]
    intro i hi j hj h
    omega

  -- Then, we can rewrite the sum $\sum_{i=0}^{199} a_i$ as
  -- $\sum_{i=0}^{99} a_{2i} + \sum_{i=0}^{99} a_{2i + 1} = \sum_{i=0}^{99} b_i.
  have h4 : ∑ i ∈ range 200, a i = ∑ i ∈ range 100, b i := by
    rw [h1, ←h2, ←h3, ←Finset.sum_add_distrib]

  -- Therefore, let's compute the sum $\sum_{i=0}^{99} b_i$ instead.
  rw [h4]

  -- Notice that $b_i = 10$ as the sum of the alternating terms $a_i$ is $10$.
  have hb (i) : b i = 10 := by
    calc _ = a (2 * i) + a (2 * i + 1) := by rfl
         _ = (-1) ^ (2 * i) * (1990 - 10 * (2 * i)) + (-1) ^ (2 * i + 1) * (1990 - 10 * (2 * i + 1)) := by simp [ha]
         _ = _ := by ring_nf; simp

  -- So, $b_i$ is just the constant 10 sequence. As there are $100$ terms in the sum, the result is
  -- $100 \times 10 = 1000$.
  simp [hb]