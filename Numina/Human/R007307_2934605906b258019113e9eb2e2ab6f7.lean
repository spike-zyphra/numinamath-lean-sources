import Mathlib

/- Chaque nombre rationnel strictement positif est colorié soit en rouge, soit en noir, de telle sorte que:

- les nombres $x$ et $x+1$ sont de couleurs différentes ;
- les nombres $x$ et $\frac{1}{x}$ sont de la même couleur;
- le nombre 1 est colorié en rouge.

Quelle est la couleur de $\frac{2012}{2013}$ ?
(On ne demande pas de démontrer l'existence d'un tel coloriage.) -/
theorem number_theory_607458 (f : ℚ → Bool) (h1 : ∀ x, f x ≠ f (x + 1))
  (h2 : ∀ x, f x = f (1/x)) (h3 : f 1 = true) :
  f (2012 / 2013) = true := by
    -- auxiliary lemma : if x is even, then f x =false, else f x =true.
    have h (x : ℕ) : (Even x → f x = false) ∧ (Odd x → f x = true) := by
      induction' x with x ind
      · simp
        have := h1 0
        simp [h3] at this
        exact this
      · rcases Nat.even_or_odd x with evenx | oddx
        · have := h1 x
          simp [evenx] at ind ⊢
          simp [ind] at this
          exact this
        · have := h1 x
          have evenxsucc : Even (x + 1) := by
            refine Nat.even_add'.mpr ?_
            tauto
          simp [oddx, evenxsucc] at ind ⊢
          simp [ind] at this
          exact this
    -- By the lemma above, f 2012 = false.
    have f1 : f 2012 = false := (h 2012).1 (by decide)
    -- According to the first rule, f (1 + 1 / 2012) = true.
    have f2 : f (1 + 1 / 2012) = true := by
      have c1 := (h2 2012).symm.trans f1
      have c2 := h1 (1 / 2012)
      rw [c1, add_comm] at c2
      rw [←Bool.not_eq_false]
      tauto
    rw [show (2012 / 2013 : ℚ) = 1 / (1 + 1 / 2012) by norm_num]
    -- According to the second rule, f (1 / (1 + 1 / 2012)) = true.
    rw [←h2 (1 + 1 / 2012), f2]
