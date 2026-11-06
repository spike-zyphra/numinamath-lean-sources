import Mathlib

/-Suppose that d is an odd integer and e is an even integer. How many of the following expressions are equal to an odd integer?
d + d,  (e + e) * d, d * d, d * (e + d)
(A) 0 (B) 1 (C) 2 (D) 3 (E) 4-/

theorem number_theory_272215 (d e : ℤ) (hd : Odd d) (he : Even e) (a: ℕ → ℤ)
 (h1: a 1 = d + d) (h2: a 2 = (e + e) * d) (h3: a 3 = d * d) (h4: a 4 = d * (e + d)):
    {i: ℕ | 1 ≤ i ∧ i ≤ 4 ∧ Odd (a i)}.encard = 2 := by

   -- we direct show that a 3 and a 4 are odd
   have h_eq: {i: ℕ | 1 ≤ i ∧ i ≤ 4 ∧ Odd (a i)} = {3, 4} := by
     ext i
     constructor
     .
       intro h
       simp at h
       rcases h with ⟨u, t, w⟩
       simp
       by_contra! s
       have v: i = 1 ∨ i = 2 := by omega
       clear s u t
       rcases v with v | v
       .
         rw [v] at w
         rw [h1] at w
         rw [show d + d = 2 * d by ring] at w
         absurd w
         simp
       .
         rw [v] at w
         rw [h2] at w
         rw [show (e + e) * d = 2 * (e * d) by ring] at w
         absurd w
         simp

     -- the backward direction
     .
      intro h
      simp at h
      rcases h with h | h
      .
        simp [h]
        rw [h3]
        apply Odd.mul
        exact hd
        exact hd
      .
         simp [h]
         rw [h4]
         apply Odd.mul
         exact hd
         rw [show e + d = d + e by ring]
         apply Even.odd_add
         exact he
         exact hd

   -- finally, count the elements
   rw [h_eq]
   simp [Set.encard]