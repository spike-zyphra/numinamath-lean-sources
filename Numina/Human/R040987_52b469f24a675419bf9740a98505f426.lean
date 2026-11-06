import Mathlib

open Finset

/-
Is it possible to find 2005 different positive square numbers such that their sum is also a square number?
-/
theorem number_theory_239316:
  ∃ S : List ℕ, ∃ p : ℕ, 
    S.length = 2005 ∧ (∀ n ∈ S, ∃ m : ℕ, n = m^2) ∧
  S.sum = p^2 := by
  -- we show this with the more general claim
  have h_list (n: ℕ) (hn: n ≥ 2):
    ∃ S : List ℕ, ∃ p : ℕ, 
    S.length = n ∧ (∀ n ∈ S, ∃ m : ℕ, n = m^2) ∧
      S.sum = p^2 := by
    -- prove by induction on n with n >= 2
    induction' n, hn using Nat.le_induction
    · -- use case, we just use [3^2, 4^2]
      use [3^2, 4^2]; use 5
      -- we can prove most of the goals since we have concrete list and they are decidable
      simp
      -- finally, we need to show that indeed 3^2 = 9 and 4^2 = 16
      refine ⟨⟨3, ?_⟩, ⟨4, ?_⟩⟩ <;> simp
    · rename_i n' hmn a_ih
      -- next we incrementally create a new list from the induction hypothesis
      obtain ⟨S, p, hsl, hsq, heq⟩ := a_ih
      have hsl_pos: 0 < S.length := by linarith
      -- since S is non empty, we can get the head of it
      obtain ⟨s, t, h_cons⟩ := List.exists_cons_of_length_pos hsl_pos
      -- also since s is in the list it is a perfect square
      obtain ⟨s', hs'⟩ := hsq s (by simp [h_cons])
      -- the new list we use adds two elements: s * 3^2 and s * 4^2, others are multiplied by 5^2
      use s*3^2 :: s*4^2 :: t.map (· * 5^2)
      use p*5
      -- we next prove each of the condition
      refine ⟨?_, ?_, ?_⟩
      · -- firstly the length is incremented by 1
        simp [<-hsl, h_cons]
      · -- secondly, all of them are perfect square number, where we prove by enumerating the position in the list
        simp; refine ⟨?_, ?_, ?_⟩
        · use s'*3; rw [hs']; linarith
        · use s'*4; rw [hs']; linarith
        · -- finally, if it is an element of the original list
          intro a ht
          -- then we can apply hsq and they must be perfect square
          specialize hsq a (by rw [h_cons]; simp; right; exact ht)
          -- here a = t'^2
          obtain ⟨t', ht'⟩ := hsq
          -- the element in the new list is simply 5^2 * t'^2 = (5t')^2
          use t'*5
          rw [ht']
          linarith
      · -- we check the summation by first multiplying the sum of S by 5^2
        have h': (S.map (· * 5^2)).sum = p^2 * 5^2 := by
          rw [S.sum_map_mul_right (f := _)]
          simp
          rw [heq]
        -- next we split S up
        rw [h_cons] at h'
        -- also rewrite (p*5)^2 to p^2*5^2, the replacing it with the map sum in h'
        rw [mul_pow, <-h']
        -- next we remove all the cons
        simp
        -- then we cancel the map sum of t (List.map (fun x => x * 25) t).sum by grouping s*9 and s*16
        simp [<-add_assoc]
        -- we are left with showing s*9 + s*16 = s*25
        linarith
  -- then we can simply apply h_list
  specialize h_list 2005 (by simp)
  obtain ⟨S, p, ⟨hA, hB, hC⟩⟩ := h_list
  use S; use p