import Mathlib

/-Given sets of real numbers $A$ and $B$, we define the operation $A \otimes B = \{ x \mid x = ab + a + b, \text{ where } a \in A, b \in B \}$.
Let $A = \{ 0, 2, 4, \cdots, 18 \}$ and $B = \{ 98, 99, 100 \}$.
What is the sum of all elements in $A \otimes B$?-/
theorem my_favorite_theorem
(A B: Finset ℤ)(f:=(fun (a b : ℤ) => a*b+a+b))
(hf: ∀(a b:ℤ), (f a b = a * b + a + b))
(hA: A = {0, 2, 4, 6, 8, 10, 12, 14, 16, 18})
(hB: B = {98, 99, 100}) :
∑ a ∈ A, ∑ b ∈ B, f a b = 29970 := by
  -- First, substitute the sets according to given hypotheses
  rw [hA, hB]
  
  -- Unfold the definition of f using hf
  simp only [hf]
  
  -- Calculate the sum
  -- For each element in A, we compute the sum over B
  have h1 : ∀ (a:ℤ),
            ∑ b ∈ {98, 99, 100}, (a * b + a + b)= 3*a + a*(98+99+100) + (98+99+100) := by
    intro a 
    simp [Finset.sum_add_distrib]
    ring
    
  -- Simplify the inner sum expression
  have h2 : ∀ a, 3*a + a*(98+99+100) + (98+99+100) = a * 297 + 3*a + 297 := by
    intro a
    ring
    
  -- Apply the simplification to every element in the outer sum
  simp_rw [h1]
  
  -- Calculate the sum of a * 297 + 3*a + 297 over A
  have h3 : ∑ a ∈ {0, 2, 4, 6, 8, 10, 12, 14, 16, 18}, (a * 297 + 3*a + 297) = 
            297 * (∑ a ∈ {0, 2, 4, 6, 8, 10, 12, 14, 16, 18}, a) + 
            3 * (∑ a ∈ {0, 2, 4, 6, 8, 10, 12, 14, 16, 18}, a) + 
            297 * 10 := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp
    
  -- Calculate the sum of elements in A
  have h4 : ∑ a ∈ {0, 2, 4, 6, 8, 10, 12, 14, 16, 18}, a = 90 := by
    simp
  rw[h4] at h3
  simp[h3]