import Mathlib

open Finset

/- 5. The faces of a 12 -sided die are numbered $1,2,3,4,5,6,7,8,9,10,11$, and 12 such that the sum of the numbers on opposite faces is 13 . The die is meticulously carved so that it is biased: the probability of obtaining a particular face $F$ is greater than $1 / 12$, the probability of obtaining the face opposite $F$ is less than $1 / 12$ while the probability of obtaining any one of the other ten faces is $1 / 12$. When two such dice are rolled, the probability of obtaining a sum of 13 is $29 / 384$. What is the probability of obtaining face $F$ ? -/
theorem algebra_218542 {p : Fin 12 → ℝ} (i : Fin 12)
  (h1 : ∀ j, p j ≥ 0) (h1 : ∑ j, p j = 1)
  (h2 : p i > 1 / 12 ∧ p (11 - i)  < 1 / 12)
  (h3 : ∀ j, j ≠ i ∧ j ≠ (11 - i) → p j = 1 / 12)
  (h4 : ∑ j, p j * p (11 - j) = 29 / 384) :
  p i = 7 / 48 := by
    let x := p i - 1 / 12
    let S : Finset (Fin 12) := Finset.univ
    let S' := (S.erase i).erase (11 - i)

    have hi : i ∈ S := Finset.mem_univ _
    have hi' : 11 - i ∈ S.erase i := by
      simp_all [S, mem_erase]
      omega

    -- The probabilities that the die lands on its corresponding faces are $\frac{1}{12}, \ldots, \frac{1}{12}, \frac{1}{12} + x$, and $\frac{1}{12} - x$, where the last two probabilities are for the face $F$ and its opposite face, respectively, while the rest are for the other faces (since these probabilities must sum up to $1$).
    have h5 : ∑ j, p j = p i + p (11 - i) + ∑ j ∈ S', p j := by
      rw [← Finset.add_sum_erase S _ hi, ← Finset.add_sum_erase _ _ hi']
      simp_all [S']
    have h6 : ∑ j ∈ S', p j = ∑ j ∈ S', (1 / 12) := by
      apply Finset.sum_congr rfl
      intros j hj
      simp only [Finset.mem_erase, Finset.mem_univ, true_and] at hj
      apply h3
      simp [S'] at hj
      omega
    have h7 : S'.card = 10 := by
      rw [Finset.card_erase_of_mem hi', Finset.card_erase_of_mem hi]
      simp [S]
    have h8 : p i = 1 / 12 + x := by simp [x]
    have h9 : p (11 - i) = 1 / 12 - x := by
      rw [h5, h6, Finset.sum_const, h7] at h1
      simp at h1
      linarith [h1, h8]

    -- Now, the sum of the results of the two dice can only be $13$ if the results shown on both dice are such that they are opposites of one another. Hence,
    --\[10\left(\frac{1}{12}\right)\left(\frac{1}{12}\right) + 2\left(\frac{1}{12} + x\right)\left(\frac{1}{12} - x\right) = \frac{29}{384}.\]
    have h10 : ∑ j, p j * p (11 - j) = 2 * p i * p (11 - i) + ∑ j ∈ S', p j * p (11 - j) := by
      rw [← Finset.add_sum_erase S _ hi, ← Finset.add_sum_erase _ _ hi']
      simp [S']
      linarith
    have h11 : ∑ j ∈ S', p j * p (11 - j) = ∑ j ∈ S', (1 / 144) := by
      apply Finset.sum_congr rfl
      intros j hj
      simp only [Finset.mem_erase, Finset.mem_univ, true_and] at hj
      simp [S'] at hj
      have : p j = 1 / 12 := by apply h3; omega
      have : p (11 - j) = 1 / 12 := by apply h3; omega
      nlinarith
    have h12 : 2 * p i * p (11 - i) + 10 / 144 = 29 / 384 := by
      rw [h10, h11, Finset.sum_const, h7] at h4
      simp at h4
      linarith [h4, h11]
    -- This leads to the quadratic equation \[\frac{1}{144} - x^2 = \frac{7}{2304}.\]
    have h12 : x ^ 2 = (1 / 16) ^ 2 := by
      rw [h8, h9] at h12
      nlinarith [h12]
    -- Solving for $x$, we get $x = \frac{1}{16}$ as the only plausible solution.  Therefore, the probability of obtaining face $F$ must be $\frac{1}{12} + \frac{1}{16} = \frac{7}{48}$.
    have h13 : x = 1 / 16 ∨ x = - (1 / 16) := eq_or_eq_neg_of_sq_eq_sq _ _ h12
    cases h13
    case inl hx => linarith
    case inr hx => linarith