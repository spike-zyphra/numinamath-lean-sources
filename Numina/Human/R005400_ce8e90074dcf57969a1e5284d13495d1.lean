import Mathlib

set_option maxRecDepth 2000

/-
How many 5-digit numbers $\overline{a b c d e}$ exist such that
digits $b$ and $d$ are each the sum of the digits to their
immediate left and right? (That is, $b=a+c$ and $d=c+e$.)
-/
theorem combinatorics_608153 :
  (((Finset.Icc 1 9) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10)).filter
    (fun (a, b, c, d, e) ↦ b = a + c ∧ d = c + e)).card = 330 := by

  let f :   (n : ℕ × ℕ × ℕ × ℕ × ℕ)
          → (n ∈ (((Finset.Icc 1 9) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10)).filter (fun (a, b, c, d, e) ↦ b = a + c ∧ d = c + e)))
          → ℕ × ℕ × ℕ := fun (a, _, c, _, e) _ ↦ (a+c, c, c+e)

  -- Suffices to show that the set of (a,b,c,d,e) where a ∈ {1,...,9} 
  -- and b,c,d,e ∈ {0,...,9} with b = a + c and d = c + e
  -- has the same cardinality as the of (b,c,d) where b,c,d ∈ {0,...,9} 
  -- with b > c and d ≥ c since the latter set
  -- is easy to count.
  suffices (((Finset.Icc 1 9) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10)).filter (fun (a, b, c, d, e) ↦ b = a + c ∧ d = c + e)).card
      = (((Finset.range 10) ×ˢ (Finset.range 10) ×ˢ (Finset.range 10)).filter (fun (b, c, d) ↦ b > c ∧ d ≥ c)).card by rw[this]; decide

  apply Finset.card_bij f
  . aesop
  . aesop
  . simp [f]
    intro b c d
    intro h1 h2 h3 h4 h5
    use b - c
    use b
    use c
    use d
    use d - c
    omega
  done
